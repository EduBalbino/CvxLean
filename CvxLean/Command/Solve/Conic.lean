import CvxLean.Lib.Minimization
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Array
import CvxLean.Lib.Math.Data.Matrix
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.ToExpr
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Util.Debug
import CvxLean.Meta.Minimization
import CvxLean.Syntax.Minimization
import CvxLean.Command.Solve.Float.Coeffs
import CvxLean.Command.Solve.Float.FloatToReal
import CvxLean.Command.Solve.Mosek.SolToSolutionData
import CvxLean.Command.Solve.Mosek.CBFOfProblemData
import CvxLean.Command.Solve.Mosek.Path

/-!
# Procedure to solve a minimization problem

This file defines how to solve an optimization problem using an external solver. The key function is
`solutionDataFromProblemData`.

Currently, we only support MOSEK, but when more solvers are added, this code will still be the entry
point of the `solve` command and it will be here where the solver is called.
-/

namespace CvxLean.Meta

open Lean Meta Minimization

/-- From a minimization expression with given problem data, proceed as follows:
1. Convert `ProblemData` to CBF format.
2. Call MOSEK by writing to a `.cbf` file.
3. Read the solution from the resulting `.sol` file.
4. Return the solution as `SolutionData`. -/
unsafe def solutionDataFromProblemData (minExpr : MinimizationExpr) (data : ProblemData)
    (sections : ScalarAffineSections) : MetaM SolutionData := do
  -- Create CBF problem.
  let cbf ← CBF.ofProblemData minExpr data sections

  -- Create files and run solver. The names are randomized to avoid race conditions when running the
  -- tests. Use /tmp to avoid issues with relative paths and missing directories.
  let r ← IO.rand 0 (2 ^ 32 - 1)
  let tempDir := System.FilePath.mk "/tmp"
  let outputPath := (tempDir / s!"cvxlean_problem{r}.sol").toString
  let inputPath := (tempDir / s!"cvxlean_problem{r}.cbf").toString

  -- Write input file.
  IO.FS.writeFile inputPath (ToString.toString cbf)

  -- Adjust path to MOSEK.
  let p := if let some p' := ← IO.getEnv "PATH" then
    if mosekBinPath != "" then p' ++ ":" ++ mosekBinPath else p'
  else
    mosekBinPath

  -- Set license path. MOSEK requires MOSEKLM_LICENSE_FILE to find the license.
  let licPath := if mosekLicensePath != "" then some mosekLicensePath else none

  -- Run solver.
  let out ← IO.Process.output {
    cmd := "mosek",
    args := #[inputPath],
    env := #[("PATH", some p), ("MOSEKLM_LICENSE_FILE", licPath)] }

  if out.exitCode != 0 then
    throwSolveError ("MOSEK exited with code " ++ ToString.toString out.exitCode ++ "\n" ++ out.stderr)

  -- Read output file after MOSEK has written to it.
  let output ← IO.FS.readFile outputPath

  match Sol.Parser.parse output with
  | Except.ok res =>
      IO.FS.removeFile inputPath
      IO.FS.removeFile outputPath
      return Sol.Result.toSolutionData res
  | Except.error err =>
      throwSolveError ("MOSEK output parsing failed. " ++ err ++ "\n\nSOL FILE CONTENT:\n" ++ output)

/-- Convert solution data back to a Lean expression representing the solution point. -/
unsafe def exprFromSolutionData (minExpr : MinimizationExpr) (solData : SolutionData) :
    MetaM Expr := do
  let vars ← decomposeDomainInstantiating minExpr

  -- Generate solution of the correct shape.
  let solPointExprArrayRaw : Array Expr :=
    Array.mk <| solData.varsSols.map (fun v => floatToReal v.value)

  -- Vectors and matrices as functions.
  let mut solPointExprArray : Array Expr := #[]

  -- TODO: This won't work in general, need to take into account the associativity of the variables
  -- if there are products, `inferDimension` might need to return a tree.
  let mut i : ℕ := 0
  for (_, varTy) in vars do
    let dims ← inferDimension varTy
    -- NOTE: This is because a var type can be a product itself. Ignore for now.
    for (n, m) in dims do
      if n = 1 ∧ m = 1 then
        -- Basic type.
        solPointExprArray := solPointExprArray.push (solPointExprArrayRaw[i]!)
        i := i + 1
      else if n ≠ 0 ∧ m = 1 then
        -- Vector.
        let exprs := (solPointExprArrayRaw.drop i).take n

        -- TODO: Code repetition.
        let arrayExpr ← Expr.mkArray (mkConst ``Real) exprs
        let arrayList ← mkAppM ``Array.toList #[arrayExpr]
        -- Default value: (0 : ℝ)
        let defaultReal := floatToReal 0.0
        let v ← withLocalDeclD `i' (← mkAppM ``Fin #[toExpr n]) fun i' => do
          let i'' := mkApp2 (mkConst ``Fin.val) (toExpr n) i'
          -- Get from generated array.
          let r ← mkAppM ``List.getD #[arrayList, i'', defaultReal]
          mkLambdaFVars #[i'] r

        solPointExprArray := solPointExprArray.push v
        i := i + n
      else
        -- Matrix.
        let mut exprs := #[]
        for j in [:m] do
          let arrayExpr ← Expr.mkArray (mkConst ``Real)
            ((solPointExprArrayRaw.drop (i + j * n)).take n)
          let listExpr ← mkAppM ``Array.toList #[arrayExpr]
          exprs := exprs.push listExpr

        let arrayListExpr ← Expr.mkArray (← mkAppM ``List #[mkConst ``Real]) exprs

        -- List of list representing the matrix.
        let listListExpr ← mkAppM ``Array.toList #[arrayListExpr]

        -- Default values
        let defaultReal := floatToReal 0.0
        let emptyList := mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Real)

        let M ← withLocalDeclD `i' (← mkAppM ``Fin #[toExpr n]) fun i' => do
          let i'' := mkApp2 (mkConst ``Fin.val) (toExpr n) i'
          let ri ← mkAppM ``List.getD #[listListExpr, i'', emptyList]
          withLocalDeclD `j' (← mkAppM ``Fin #[toExpr m]) fun j' => do
            let j'' := mkApp2 (mkConst ``Fin.val) (toExpr m) j'
            let rij ← mkAppM ``List.getD #[ri, j'', defaultReal]
            mkLambdaFVars #[i', j'] rij

        solPointExprArray := solPointExprArray.push M
        i := i + n * m

  let solPointExpr : Expr ← Lean.Expr.mkProd solPointExprArray
  return solPointExpr

end CvxLean.Meta
