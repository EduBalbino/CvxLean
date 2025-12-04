import CvxLean.Command.Solve.Mosek.SolveIO

/-!
# Test: 2D Bisection with Two Bilinear Parameters

This file demonstrates how to use the Pure IO Solver for **bisection on two parameters**.
This is the key use case for problems with bilinear terms that need to be handled via
parameter sweeps or bisection.

## Problem Structure

Given a problem parameterized by `(γ₁, γ₂)`:

```
Minimize f(x)
Subject to:
  g_i(x, γ₁, γ₂) ∈ Cone_i
```

Where constraints may have bilinear terms like `γ₁ * γ₂ * x`, the idea is to:
1. Fix one parameter and bisect on the other
2. Alternate or use a 2D search strategy
3. Find the feasibility boundary in the (γ₁, γ₂) space

## Key Insight

The `ProblemData` construction is **pure Lean** (no MetaM/elaboration needed), so you can
freely build problem instances at runtime with any Float parameters. This enables:
- Bisection loops in IO
- Grid searches
- Optimization over the parameter space
- Any iterative algorithm you want!
-/

namespace CvxLean.Test.SolveIOBisection2D

open CvxLean

/-! ## Example 1: Box-Constrained Feasibility with Two Bounds

Find the Pareto frontier of feasible (γ₁, γ₂) pairs where:

  x + y >= γ₁
  2x + y <= γ₂
  x, y >= 0

Feasible when γ₂ >= γ₁ (roughly, depending on the specific problem).
-/

/-- Build problem data parameterized by two bounds (γ₁, γ₂).

    This represents a feasibility problem where:
    - Lower bound on sum: x + y >= γ₁
    - Upper bound on weighted sum: 2x + y <= γ₂
    - Non-negativity: x, y >= 0
-/
def boxFeasibility (γ₁ γ₂ : Float) : ProblemData :=
  ProblemData.empty
    -- Feasibility problem: zero objective
    |>.setObjectiveOnlyVector #[0.0, 0.0] 0.0
    -- x + y >= γ₁  ⟹  x + y - γ₁ >= 0
    |>.addPosOrthConstraint #[1.0, 1.0] (-γ₁)
    -- 2x + y <= γ₂  ⟹  -(2x + y) + γ₂ >= 0
    |>.addPosOrthConstraint #[-2.0, -1.0] γ₂
    -- x >= 0
    |>.addPosOrthConstraint #[1.0, 0.0] 0.0
    -- y >= 0
    |>.addPosOrthConstraint #[0.0, 1.0] 0.0

def boxFeasibilitySections : ScalarAffineSections := #[1, 2, 3, 4]
def boxFeasibilityDim : Nat := 2

/-- Wrapped as ParameterizedProblem for use with bisection utilities -/
def boxFeasibilityProblem : ParameterizedProblem (Float × Float) := {
  build := fun (γ₁, γ₂) => boxFeasibility γ₁ γ₂
  sections := boxFeasibilitySections
  totalDim := boxFeasibilityDim
  description := "Box feasibility: find (γ₁, γ₂) boundary"
}

/-- Test grid search to visualize feasibility region -/
def testGridSearch : IO Unit := do
  IO.println "=== Grid Search: Visualize Feasibility Region ==="
  IO.println "Checking feasibility of boxFeasibility(γ₁, γ₂) on a grid..."
  IO.println ""

  -- Header
  IO.print "γ₁\\γ₂ |"
  for γ₂ in [0.0, 2.0, 4.0, 6.0, 8.0, 10.0] do
    IO.print s!" {γ₂}  "
  IO.println ""
  IO.println ("------|" ++ "------------------------------------")

  -- Grid
  for γ₁ in [0.0, 2.0, 4.0, 6.0, 8.0, 10.0] do
    IO.print s!" {γ₁}  |"
    for γ₂ in [0.0, 2.0, 4.0, 6.0, 8.0, 10.0] do
      let feasible ← boxFeasibilityProblem.isFeasibleAt (γ₁, γ₂)
      let symbol := if feasible then " ✓  " else " ✗  "
      IO.print symbol
    IO.println ""
  IO.println ""

/-! ## Example 2: Manual 2D Bisection

Demonstrate how to write your own 2D bisection loop over (γ₁, γ₂).

**Your custom logic goes here!** This is just a template.
-/

/-- Custom 2D bisection: alternating coordinate descent on feasibility boundary.

    This finds a point on the boundary where increasing either γ₁ or γ₂
    makes the problem infeasible.

    **This is a template for your bilinear parameter search!** -/
def customBisect2D (prob : ParameterizedProblem (Float × Float))
    (γ₁_lo γ₁_hi γ₂_lo γ₂_hi : Float)
    (tol : Float := 0.01) (maxOuterIters : Nat := 10) (maxInnerIters : Nat := 20)
    : IO (Float × Float × Nat) := do
  let mut γ₁ := (γ₁_lo + γ₁_hi) / 2
  let mut γ₂ := (γ₂_lo + γ₂_hi) / 2
  let mut totalCalls := 0

  IO.println s!"Starting 2D bisection from (γ₁={γ₁}, γ₂={γ₂})..."

  for outer in [:maxOuterIters] do
    let prevγ₁ := γ₁
    let prevγ₂ := γ₂

    -- Phase 1: Bisect on γ₁ with γ₂ fixed
    -- Find max γ₁ such that problem is feasible
    let mut lo₁ := γ₁_lo
    let mut hi₁ := γ₁_hi
    for _ in [:maxInnerIters] do
      if hi₁ - lo₁ < tol then break
      let mid := (lo₁ + hi₁) / 2
      let feas ← prob.isFeasibleAt (mid, γ₂)
      totalCalls := totalCalls + 1
      if feas then lo₁ := mid else hi₁ := mid
    γ₁ := (lo₁ + hi₁) / 2

    -- Phase 2: Bisect on γ₂ with γ₁ fixed
    -- Find min γ₂ such that problem is feasible (for this problem structure)
    let mut lo₂ := γ₂_lo
    let mut hi₂ := γ₂_hi
    for _ in [:maxInnerIters] do
      if hi₂ - lo₂ < tol then break
      let mid := (lo₂ + hi₂) / 2
      let feas ← prob.isFeasibleAt (γ₁, mid)
      totalCalls := totalCalls + 1
      if feas then hi₂ := mid else lo₂ := mid
    γ₂ := (lo₂ + hi₂) / 2

    IO.println s!"  Iter {outer}: (γ₁={γ₁}, γ₂={γ₂})"

    -- Convergence check
    if Float.abs (γ₁ - prevγ₁) < tol ∧ Float.abs (γ₂ - prevγ₂) < tol then
      IO.println s!"  Converged at iteration {outer}!"
      break

  return (γ₁, γ₂, totalCalls)

/-- Test custom 2D bisection -/
def testCustomBisect2D : IO Unit := do
  IO.println "=== Custom 2D Bisection ==="
  let (γ₁, γ₂, calls) ← customBisect2D boxFeasibilityProblem 0.0 10.0 0.0 20.0 0.1 10 20
  IO.println s!"Result: (γ₁={γ₁}, γ₂={γ₂}) after {calls} solver calls"

  -- Verify result
  let feas ← boxFeasibilityProblem.isFeasibleAt (γ₁, γ₂)
  IO.println s!"Verification: feasible = {feas}"
  IO.println ""

/-! ## Example 3: Bilinear-Style Problem

A more realistic example where BOTH parameters appear in the SAME constraint,
creating a bilinear-like structure.

Problem:
  Minimize x + y
  Subject to:
    γ₁ * x + γ₂ * y >= 1   (both params in one constraint!)
    x <= 10
    y <= 10
    x, y >= 0
-/

/-- Problem with both parameters in the same constraint -/
def bilinearStyleLP (γ₁ γ₂ : Float) : ProblemData :=
  ProblemData.empty
    |>.setObjectiveOnlyVector #[1.0, 1.0] 0.0
    -- γ₁ * x + γ₂ * y >= 1  (this is where both params interact!)
    |>.addPosOrthConstraint #[γ₁, γ₂] (-1.0)
    -- x <= 10  ⟹  -x + 10 >= 0
    |>.addPosOrthConstraint #[-1.0, 0.0] 10.0
    -- y <= 10
    |>.addPosOrthConstraint #[0.0, -1.0] 10.0
    -- x >= 0
    |>.addPosOrthConstraint #[1.0, 0.0] 0.0
    -- y >= 0
    |>.addPosOrthConstraint #[0.0, 1.0] 0.0

def bilinearStyleSections : ScalarAffineSections := #[1, 2, 3, 4, 5]

def bilinearStyleProblem : ParameterizedProblem (Float × Float) := {
  build := fun (γ₁, γ₂) => bilinearStyleLP γ₁ γ₂
  sections := bilinearStyleSections
  totalDim := 2
  description := "Bilinear-style: γ₁*x + γ₂*y >= 1"
}

/-- Explore the optimal value landscape -/
def testBilinearLandscape : IO Unit := do
  IO.println "=== Bilinear-Style Problem: Optimal Value Landscape ==="
  IO.println "For γ₁*x + γ₂*y >= 1, the optimal value of (x+y) depends on (γ₁, γ₂)."
  IO.println ""

  for (γ₁, γ₂) in [(0.1, 0.1), (0.5, 0.5), (1.0, 1.0), (0.1, 1.0), (1.0, 0.1), (0.01, 0.01)] do
    let result ← bilinearStyleProblem.solveAt (γ₁, γ₂)
    match result with
    | .success sol =>
        if sol.status == "PRIMAL_AND_DUAL_FEASIBLE" then
          -- Compute objective value
          let vals := sol.varsSols.map (·.value)
          let objVal := vals.foldl (· + ·) 0.0
          IO.println s!"  (γ₁={γ₁}, γ₂={γ₂}): opt_val = {objVal}"
        else
          IO.println s!"  (γ₁={γ₁}, γ₂={γ₂}): {sol.status}"
    | _ => IO.println s!"  (γ₁={γ₁}, γ₂={γ₂}): SOLVE_FAILED"
  IO.println ""

/-! ## Example 4: YOUR TEMPLATE for True Bilinear Bisection

Here's a skeleton you can fill in for your specific bilinear problem.
The key idea:

1. Define `yourBilinearProblem : Float → Float → ProblemData`
2. Choose your bisection strategy (independent, coupled, golden section, etc.)
3. Implement the loop using `solveProblemDataIO` or `ParameterizedProblem.isFeasibleAt`
-/

/-- **TEMPLATE**: Your bilinear problem goes here.

    Replace this with your actual problem structure.
    The key is that γ₁ and γ₂ can appear anywhere in the coefficients! -/
def yourBilinearProblem (γ₁ γ₂ : Float) : ProblemData :=
  -- EXAMPLE: A problem where we're trying to find params that make
  -- some matrix positive definite, or some constraint feasible.
  ProblemData.empty
    |>.setObjectiveOnlyVector #[1.0, 0.0, 0.0] 0.0  -- 3 variables
    -- YOUR CONSTRAINTS HERE, using γ₁ and γ₂ in the coefficients
    -- Example: γ₁ * x₁ + x₂ >= γ₂
    |>.addPosOrthConstraint #[γ₁, 1.0, 0.0] (-γ₂)
    -- Example: x₁ + γ₂ * x₃ <= 10
    |>.addPosOrthConstraint #[-1.0, 0.0, -γ₂] 10.0
    -- Non-negativity
    |>.addPosOrthConstraint #[1.0, 0.0, 0.0] 0.0
    |>.addPosOrthConstraint #[0.0, 1.0, 0.0] 0.0
    |>.addPosOrthConstraint #[0.0, 0.0, 1.0] 0.0

def yourBilinearSections : ScalarAffineSections := #[1, 2, 3, 4, 5]

/-- **TEMPLATE**: Your custom bisection strategy.

    Ideas:
    - Binary search on a 1D "line" through (γ₁, γ₂) space
    - Coordinate descent: alternate bisecting γ₁ and γ₂
    - Golden section search in 2D
    - Gradient-free optimization (Nelder-Mead, etc.)
-/
def yourBisectionStrategy (γ₁_init γ₂_init : Float) : IO (Float × Float) := do
  let prob : ParameterizedProblem (Float × Float) := {
    build := fun (g1, g2) => yourBilinearProblem g1 g2
    sections := yourBilinearSections
    totalDim := 3  -- 3 variables in this example
  }

  -- YOUR BISECTION LOGIC HERE
  -- This is just a placeholder that does a simple feasibility check
  let feas ← prob.isFeasibleAt (γ₁_init, γ₂_init)
  IO.println s!"Initial point ({γ₁_init}, {γ₂_init}) feasible: {feas}"

  -- Return the initial point (replace with your actual bisection result)
  return (γ₁_init, γ₂_init)

/-! ## Main Test Runner -/

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     CvxLean Pure IO Solver Tests - 2D Bisection              ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  testGridSearch
  testCustomBisect2D
  testBilinearLandscape

  IO.println "=== Template Test ==="
  let _ ← yourBisectionStrategy 1.0 1.0
  IO.println ""

  IO.println "All 2D bisection tests completed!"
  IO.println ""
  IO.println "To use these utilities in your own code:"
  IO.println "  1. Define your problem as `ProblemData` parameterized by (γ₁, γ₂)"
  IO.println "  2. Wrap it in `ParameterizedProblem (Float × Float)`"
  IO.println "  3. Implement your bisection loop using `isFeasibleAt` or `solveAt`"
  IO.println "  4. Everything runs in pure IO - no elaboration needed!"

-- Uncomment to run:
-- #eval main

end CvxLean.Test.SolveIOBisection2D
