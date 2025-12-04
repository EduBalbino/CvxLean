import CvxLean.Command.Solve.Float.ProblemData
import CvxLean.Command.Solve.Float.SolutionData
import CvxLean.Command.Solve.Mosek.CBF
import CvxLean.Command.Solve.Mosek.Sol
import CvxLean.Command.Solve.Mosek.SolToSolutionData
import CvxLean.Command.Solve.Mosek.Path

/-!
# Pure IO Solver for MOSEK

This module provides a pure `IO`-based interface to call MOSEK, bypassing the `MetaM` monad.
This enables **runtime solving** and **iterative algorithms** like bisection that need to
call the solver multiple times with different parameters.

## Key Functions

- `solveProblemDataIO`: Takes numerical `ProblemData` and returns `SolutionData` in pure `IO`.
- `CBF.ofProblemDataPure`: Converts `ProblemData` to CBF format without `MetaM` dependency.

## Usage Example

```lean
-- Define a parameterized problem as ProblemData
def myProblem (γ : Float) : ProblemData :=
  ProblemData.empty
    |>.setObjectiveOnlyVector #[1.0, γ] 0.0
    |>.addPosOrthConstraint #[1.0, 0.0] (-1.0)

-- Solve at runtime
def main : IO Unit := do
  let sol ← solveProblemDataIO (myProblem 2.5) #[1] 2
  IO.println s!"Status: {sol.status}"
```

## Bisection Support

For bisection on parameters `(γ₁, γ₂)`, construct your `ProblemData` as a function of these
parameters, then use `solveProblemDataIO` in a loop:

```lean
def bisect2D (f : Float → Float → ProblemData) (sections : ScalarAffineSections) (dim : Nat)
    : IO (Float × Float) := do
  -- Your bisection logic here, calling:
  -- let sol ← solveProblemDataIO (f γ₁ γ₂) sections dim
  ...
```
-/

namespace CvxLean

/-! ## CBF Construction (Pure) -/

namespace CBF

/-- Translate generic cone types to MOSEK cones. Pure version (no MetaM). -/
def translateConePure : ScalarConeType → CBF.ConeType
  | ScalarConeType.Zero => CBF.ConeType.LEq
  | ScalarConeType.PosOrth => CBF.ConeType.LPos
  | ScalarConeType.Exp => CBF.ConeType.EXP
  | ScalarConeType.Q => CBF.ConeType.Q
  | ScalarConeType.QR => CBF.ConeType.QR

/-- Group consecutive cones together based on sections. Pure version.
    Returns `none` if sections are invalid. -/
def groupConesPure (sections : ScalarAffineSections) (l : List CBF.Cone) : Option (List CBF.Cone) :=
  Id.run do
    let l := l.toArray
    let mut res := []
    let mut currIdx := 0
    for idx in sections.toList do
      let group := l[currIdx:idx]
      if h : group.size > 0 then
        let c := group.get ⟨0, h⟩
        let coneType := c.type
        -- Check all cones in group have same type
        let allSameType := group.all (fun c' => c'.type == coneType)
        if !allSameType then return none
        let totalDim := group.foldl (fun acc c => acc + c.dim) 0
        currIdx := idx
        res := res ++ [CBF.Cone.mk coneType totalDim]
      else
        return none
    return some res

/-- Convert numerical problem data to CBF format. Pure version (no MetaM).

    **Parameters:**
    - `totalDim`: Total number of scalar optimization variables.
    - `data`: The numerical problem data containing objective and constraints.
    - `sections`: Indices indicating how to group consecutive constraints into cones.

    **Returns:** `Option CBF.Problem` - `none` if cone grouping fails. -/
def ofProblemDataPure (totalDim : Nat) (data : ProblemData) (sections : ScalarAffineSections)
    : Option CBF.Problem := Id.run do
  let mut cbf := CBF.Problem.empty
  cbf := cbf.addScalarVariable (CBF.Cone.mk CBF.ConeType.F totalDim)

  -- Set objective
  if h : data.objective.isSome then
    let sa := data.objective.get h
    let AEnc := CBF.EncodedMatrixList.fromArray #[sa.A]
    let aEnc := CBF.EncodedVector.fromArray sa.a
    let bEnc := CBF.EncodedValue.mk (some sa.b)
    cbf := cbf.setObjectivePSDVariablesCoord AEnc
    cbf := cbf.setObjectiveScalarVariablesCoord aEnc
    cbf := cbf.setObjectiveShiftCoord bEnc

  -- Add scalar affine constraints
  for (sa, sct) in data.scalarAffineConstraints do
    let coneType := translateConePure sct
    let cone := CBF.Cone.mk coneType 1
    let AEnc := CBF.EncodedMatrixList.fromArray #[sa.A]
    let aEnc := CBF.EncodedVector.fromArray sa.a
    let bEnc := sa.b
    cbf := cbf.addScalarValuedAffineConstraint cone AEnc aEnc bEnc

  -- Add matrix affine constraints (PSD cones)
  for ma in data.matrixAffineConstraints do
    let HEnc := CBF.EncodedMatrixList.fromArray ma.H
    let DEnc := CBF.EncodedMatrix.fromArray ma.D
    cbf := cbf.addMatrixValuedAffineConstraint ma.n HEnc DEnc

  -- Group cones appropriately
  let n := cbf.scalarConstraints.n
  let cones := cbf.scalarConstraints.cones
  match groupConesPure sections cones with
  | some groupedCones =>
      cbf := cbf.setScalarConstraints (CBF.ConeProduct.mk n groupedCones.length groupedCones)
      return some cbf
  | none => return none

end CBF

/-! ## Pure IO Solver -/

/-- Configuration for the MOSEK solver. -/
structure MosekConfig where
  /-- Path to MOSEK binary directory. If empty, uses system PATH. -/
  binPath : String := mosekBinPath
  /-- Path to MOSEK license file. If empty, uses default location. -/
  licensePath : String := mosekLicensePath
  /-- Directory for temporary files. -/
  tempDir : System.FilePath := "/tmp"
  /-- Whether to keep temporary files after solving (useful for debugging). -/
  keepTempFiles : Bool := false
  deriving Repr, Inhabited

/-- Default MOSEK configuration using paths from `Path.lean`. -/
def MosekConfig.default : MosekConfig := {}

/-- Result of a solve operation. -/
inductive SolveResult
  /-- Successful solve with solution data. -/
  | success (sol : SolutionData)
  /-- CBF construction failed (invalid sections or problem structure). -/
  | cbfError (msg : String)
  /-- MOSEK execution failed. -/
  | mosekError (exitCode : UInt32) (stderr : String)
  /-- Solution file parsing failed. -/
  | parseError (msg : String)

namespace SolveResult

/-- Check if the solve was successful. -/
def isSuccess : SolveResult → Bool
  | success _ => true
  | _ => false

/-- Check if the problem was feasible (primal and dual). -/
def isFeasible : SolveResult → Bool
  | success sol => sol.status == "PRIMAL_AND_DUAL_FEASIBLE"
  | _ => false

/-- Get solution data if successful, otherwise `none`. -/
def toSolutionData? : SolveResult → Option SolutionData
  | success sol => some sol
  | _ => none

/-- Get status string. -/
def status : SolveResult → String
  | success sol => sol.status
  | cbfError msg => s!"CBF_ERROR: {msg}"
  | mosekError code stderr => s!"MOSEK_ERROR({code}): {stderr}"
  | parseError msg => s!"PARSE_ERROR: {msg}"

/-- Get variable values if successful and feasible. -/
def varValues? (r : SolveResult) : Option (List Float) :=
  match r with
  | success sol =>
      if sol.status == "PRIMAL_AND_DUAL_FEASIBLE"
      then some (sol.varsSols.map (·.value))
      else none
  | _ => none

end SolveResult

/-- Solve a problem specified by `ProblemData` using MOSEK. Pure `IO` interface.

    **Parameters:**
    - `data`: Numerical problem data (objective + constraints).
    - `sections`: Cone grouping indices.
    - `totalDim`: Total number of scalar optimization variables.
    - `config`: MOSEK configuration (optional, uses defaults).

    **Returns:** `SolveResult` indicating success or failure mode.

    **Example:**
    ```lean
    def myProblem : ProblemData :=
      ProblemData.empty
        |>.setObjectiveOnlyVector #[1.0, 2.0] 0.0
        |>.addPosOrthConstraint #[1.0, 0.0] (-1.0)

    #eval do
      let result ← solveProblemDataIO myProblem #[1] 2
      IO.println (result.status)
    ```
-/
def solveProblemDataIO (data : ProblemData) (sections : ScalarAffineSections) (totalDim : Nat)
    (config : MosekConfig := MosekConfig.default) : IO SolveResult := do
  -- Build CBF
  let some cbf := CBF.ofProblemDataPure totalDim data sections
    | return .cbfError "Failed to construct CBF (invalid sections or problem structure)"

  -- Generate random file names to avoid race conditions
  let r ← IO.rand 0 (2 ^ 32 - 1)
  let inputPath := (config.tempDir / s!"cvxlean_io_problem{r}.cbf").toString
  let outputPath := (config.tempDir / s!"cvxlean_io_problem{r}.sol").toString

  -- Write CBF file
  IO.FS.writeFile inputPath (ToString.toString cbf)

  -- Prepare environment
  let pathEnv := if let some p := ← IO.getEnv "PATH" then
    if config.binPath != "" then p ++ ":" ++ config.binPath else p
  else
    config.binPath
  let licEnv := if config.licensePath != "" then some config.licensePath else none

  -- Run MOSEK
  let out ← IO.Process.output {
    cmd := "mosek",
    args := #[inputPath],
    env := #[("PATH", some pathEnv), ("MOSEKLM_LICENSE_FILE", licEnv)]
  }

  if out.exitCode != 0 then
    unless config.keepTempFiles do
      try IO.FS.removeFile inputPath catch _ => pure ()
    return .mosekError out.exitCode out.stderr

  -- Read and parse solution
  let output ← IO.FS.readFile outputPath

  -- Cleanup temp files
  unless config.keepTempFiles do
    try IO.FS.removeFile inputPath catch _ => pure ()
    try IO.FS.removeFile outputPath catch _ => pure ()

  match Sol.Parser.parse output with
  | .ok res => return .success (Sol.Result.toSolutionData res)
  | .error err => return .parseError err

/-- Simplified solver that throws on error. Use when you expect success.

    **Throws:** `IO.Error` if solving fails for any reason. -/
def solveProblemDataIO! (data : ProblemData) (sections : ScalarAffineSections) (totalDim : Nat)
    (config : MosekConfig := MosekConfig.default) : IO SolutionData := do
  match ← solveProblemDataIO data sections totalDim config with
  | .success sol => return sol
  | .cbfError msg => throw (IO.userError s!"CBF construction failed: {msg}")
  | .mosekError code stderr => throw (IO.userError s!"MOSEK failed (exit {code}): {stderr}")
  | .parseError msg => throw (IO.userError s!"Solution parsing failed: {msg}")

/-! ## Convenience Functions for Parameterized Problems -/

/-- A parameterized optimization problem is a function from parameters to problem data.
    This structure bundles the problem constructor with metadata needed for solving. -/
structure ParameterizedProblem (P : Type) where
  /-- Construct problem data from parameters. -/
  build : P → ProblemData
  /-- Cone section indices (typically constant across parameters). -/
  sections : ScalarAffineSections
  /-- Total dimension of optimization variables. -/
  totalDim : Nat
  /-- Optional description for debugging/logging. -/
  description : String := ""

/-- Solve a parameterized problem at a specific parameter value. -/
def ParameterizedProblem.solveAt {P : Type} (prob : ParameterizedProblem P) (params : P)
    (config : MosekConfig := MosekConfig.default) : IO SolveResult :=
  solveProblemDataIO (prob.build params) prob.sections prob.totalDim config

/-- Solve a parameterized problem, throwing on error. -/
def ParameterizedProblem.solveAt! {P : Type} (prob : ParameterizedProblem P) (params : P)
    (config : MosekConfig := MosekConfig.default) : IO SolutionData :=
  solveProblemDataIO! (prob.build params) prob.sections prob.totalDim config

/-- Check if a parameterized problem is feasible at given parameters. -/
def ParameterizedProblem.isFeasibleAt {P : Type} (prob : ParameterizedProblem P) (params : P)
    (config : MosekConfig := MosekConfig.default) : IO Bool := do
  let result ← prob.solveAt params config
  return result.isFeasible

/-! ## Bisection Utilities -/

/-- Result of a 1D bisection search. -/
structure Bisection1DResult where
  /-- The parameter value found. -/
  value : Float
  /-- Number of iterations performed. -/
  iterations : Nat
  /-- Final interval width. -/
  tolerance : Float
  /-- Whether the final value yields a feasible problem. -/
  feasibleAtValue : Bool
  deriving Repr

/-- Perform 1D bisection to find the boundary between feasible and infeasible regions.

    **Parameters:**
    - `prob`: Parameterized problem with `Float` parameter.
    - `lo`, `hi`: Initial search interval.
    - `tol`: Stop when interval width < tol.
    - `maxIters`: Maximum number of iterations.
    - `feasibleAtLo`: If `true`, search assumes `lo` is feasible and `hi` is infeasible.
                      If `false`, assumes `lo` is infeasible and `hi` is feasible.

    **Returns:** The boundary parameter value and metadata. -/
def bisect1D (prob : ParameterizedProblem Float)
    (lo hi : Float) (tol : Float := 1e-6) (maxIters : Nat := 100)
    (feasibleAtLo : Bool := true) (config : MosekConfig := MosekConfig.default)
    : IO Bisection1DResult := do
  -- Use iterative loop instead of recursion for simplicity
  let mut currLo := lo
  let mut currHi := hi
  let mut itersDone := 0

  for _ in [:maxIters] do
    if currHi - currLo < tol then break
    let mid := (currLo + currHi) / 2
    let midFeasible ← prob.isFeasibleAt mid config
    itersDone := itersDone + 1
    if feasibleAtLo then
      -- Feasible at low end, searching for upper boundary
      if midFeasible then currLo := mid else currHi := mid
    else
      -- Feasible at high end, searching for lower boundary
      if midFeasible then currHi := mid else currLo := mid

  let finalMid := (currLo + currHi) / 2
  let feas ← prob.isFeasibleAt finalMid config
  return { value := finalMid, iterations := itersDone, tolerance := currHi - currLo, feasibleAtValue := feas }

/-- Result of a 2D bisection/search. -/
structure Bisection2DResult where
  /-- The parameter values found. -/
  value : Float × Float
  /-- Number of solver calls made. -/
  solverCalls : Nat
  /-- Whether the final value yields a feasible problem. -/
  feasibleAtValue : Bool
  deriving Repr

/-- Perform 2D bisection on two parameters independently.

    This performs bisection on each parameter while holding the other fixed,
    iterating until convergence. Suitable for problems where the feasibility
    boundary is monotonic in each parameter.

    **Parameters:**
    - `prob`: Parameterized problem with `(Float × Float)` parameters `(γ₁, γ₂)`.
    - `lo1`, `hi1`: Search interval for first parameter.
    - `lo2`, `hi2`: Search interval for second parameter.
    - `tol`: Convergence tolerance.
    - `maxIters`: Maximum iterations per parameter.

    **Note:** For non-separable bilinear constraints, you may need a custom search
    strategy. This function provides a starting point. -/
def bisect2DIndependent (prob : ParameterizedProblem (Float × Float))
    (lo1 hi1 lo2 hi2 : Float) (tol : Float := 1e-6) (maxIters : Nat := 50)
    (config : MosekConfig := MosekConfig.default)
    : IO Bisection2DResult := do
  let mut γ1 := (lo1 + hi1) / 2
  let mut γ2 := (lo2 + hi2) / 2
  let mut calls := 0
  let mut prevγ1 := γ1 + 2 * tol  -- Force at least one iteration
  let mut prevγ2 := γ2 + 2 * tol

  for _ in [:maxIters] do
    if Float.abs (γ1 - prevγ1) < tol ∧ Float.abs (γ2 - prevγ2) < tol then break
    prevγ1 := γ1
    prevγ2 := γ2

    -- Bisect on γ1 with γ2 fixed
    let prob1 : ParameterizedProblem Float := {
      build := fun g1 => prob.build (g1, γ2)
      sections := prob.sections
      totalDim := prob.totalDim
    }
    let res1 ← bisect1D prob1 lo1 hi1 tol maxIters true config
    γ1 := res1.value
    calls := calls + res1.iterations

    -- Bisect on γ2 with γ1 fixed
    let prob2 : ParameterizedProblem Float := {
      build := fun g2 => prob.build (γ1, g2)
      sections := prob.sections
      totalDim := prob.totalDim
    }
    let res2 ← bisect1D prob2 lo2 hi2 tol maxIters true config
    γ2 := res2.value
    calls := calls + res2.iterations

  let feas ← prob.isFeasibleAt (γ1, γ2) config
  return { value := (γ1, γ2), solverCalls := calls, feasibleAtValue := feas }

end CvxLean
