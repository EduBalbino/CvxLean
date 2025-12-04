import CvxLean.Command.Solve.Mosek.SolveIO

/-!
# Test: Pure IO Solver for Linear Programs

This file demonstrates using `solveProblemDataIO` for runtime solving of linear programs.
The key advantage is that you can call the solver from pure `IO` without needing
elaboration-time constructs.

## What This Tests

1. **Basic LP solving** via `solveProblemDataIO`
2. **Parameterized problems** where coefficients depend on runtime values
3. **Feasibility checking** via `SolveResult.isFeasible`
-/

namespace CvxLean.Test.SolveIOLinear

open CvxLean

/-! ## Test 1: Simple 2-variable LP

Minimize: x + 2y
Subject to:
  x + y >= 1
  x >= 0
  y >= 0

Optimal: x* = 1, y* = 0, value = 1
-/

/-- Build problem data for a simple 2-variable LP.

    The conic form is:
    - Minimize: c^T x  where c = [1, 2]
    - Subject to: x + y - 1 >= 0  (positive orthant)
                  x >= 0          (positive orthant)
                  y >= 0          (positive orthant)
-/
def simpleLP : ProblemData :=
  ProblemData.empty
    -- Objective: minimize x + 2y (coefficients for [x, y], constant term 0)
    |>.setObjectiveOnlyVector #[1.0, 2.0] 0.0
    -- Constraint: x + y >= 1  ⟹  x + y - 1 >= 0  ⟹  -(-x - y + 1) >= 0
    -- In PosOrth form: a^T x + b >= 0, so a = [1, 1], b = -1
    |>.addPosOrthConstraint #[1.0, 1.0] (-1.0)
    -- Constraint: x >= 0
    |>.addPosOrthConstraint #[1.0, 0.0] 0.0
    -- Constraint: y >= 0
    |>.addPosOrthConstraint #[0.0, 1.0] 0.0

/-- Sections: each constraint is in its own 1-dimensional positive orthant cone -/
def simpleLPSections : ScalarAffineSections := #[1, 2, 3]

/-- Total dimension: 2 variables (x, y) -/
def simpleLPDim : Nat := 2

/-- Test solving the simple LP -/
def testSimpleLP : IO Unit := do
  IO.println "=== Test 1: Simple 2-variable LP ==="
  let result ← solveProblemDataIO simpleLP simpleLPSections simpleLPDim
  IO.println s!"Status: {result.status}"
  match result with
  | .success sol =>
      IO.println s!"Solution status: {sol.status}"
      for v in sol.varsSols do
        IO.println s!"  {v.name} = {v.value}"
  | _ => IO.println "  Solve failed!"
  IO.println ""

/-! ## Test 2: Parameterized LP

A problem parameterized by γ ∈ ℝ:

Minimize: x + y
Subject to:
  x + y >= γ    (parametric RHS)
  x >= 0
  y >= 0

For γ <= 0: optimal value = 0 (at origin)
For γ > 0: optimal value = γ (on the line x + y = γ)
-/

/-- Build a parameterized LP where the constraint RHS depends on γ.

    **Key Point**: This function creates `ProblemData` at runtime based on the
    parameter value. No elaboration needed! -/
def parameterizedLP (γ : Float) : ProblemData :=
  ProblemData.empty
    |>.setObjectiveOnlyVector #[1.0, 1.0] 0.0
    -- Constraint: x + y >= γ  ⟹  x + y - γ >= 0
    |>.addPosOrthConstraint #[1.0, 1.0] (-γ)
    |>.addPosOrthConstraint #[1.0, 0.0] 0.0
    |>.addPosOrthConstraint #[0.0, 1.0] 0.0

/-- Test the parameterized LP at various γ values -/
def testParameterizedLP : IO Unit := do
  IO.println "=== Test 2: Parameterized LP (varying γ) ==="
  for γ in [0.0, 1.0, 2.0, 5.0, 10.0] do
    let data := parameterizedLP γ
    let result ← solveProblemDataIO data simpleLPSections simpleLPDim
    let statusStr := if result.isFeasible then "FEASIBLE" else "INFEASIBLE/ERROR"
    match result.varValues? with
    | some vals =>
        let optVal := vals.foldl (· + ·) 0.0  -- x + y
        IO.println s!"  γ = {γ}: {statusStr}, optimal value ≈ {optVal}"
    | none =>
        IO.println s!"  γ = {γ}: {statusStr}"
  IO.println ""

/-! ## Test 3: Feasibility Bisection

Find the maximum γ such that the following is feasible:

  x + y <= 10
  x + y >= γ
  x, y >= 0

Clearly, max feasible γ = 10.
-/

/-- LP that becomes infeasible when γ > 10 -/
def boundedLP (γ : Float) : ProblemData :=
  ProblemData.empty
    |>.setObjectiveOnlyVector #[0.0, 0.0] 0.0  -- Feasibility problem
    -- x + y <= 10  ⟹  -(x + y) + 10 >= 0
    |>.addPosOrthConstraint #[-1.0, -1.0] 10.0
    -- x + y >= γ
    |>.addPosOrthConstraint #[1.0, 1.0] (-γ)
    |>.addPosOrthConstraint #[1.0, 0.0] 0.0
    |>.addPosOrthConstraint #[0.0, 1.0] 0.0

def boundedLPSections : ScalarAffineSections := #[1, 2, 3, 4]

/-- Use ParameterizedProblem structure for bisection -/
def boundedLPProblem : ParameterizedProblem Float := {
  build := boundedLP
  sections := boundedLPSections
  totalDim := 2
  description := "Bounded LP: find max γ such that x+y >= γ and x+y <= 10"
}

/-- Test bisection to find maximum feasible γ -/
def testBisection : IO Unit := do
  IO.println "=== Test 3: Bisection for Feasibility Boundary ==="
  IO.println "Finding max γ such that (x + y >= γ) ∧ (x + y <= 10) is feasible..."

  -- Manual bisection for demonstration
  let mut lo := 0.0
  let mut hi := 20.0
  for i in [:20] do
    let mid := (lo + hi) / 2
    let feasible ← boundedLPProblem.isFeasibleAt mid
    IO.println s!"  Iter {i}: γ = {mid}, feasible = {feasible}"
    if feasible then lo := mid else hi := mid

  IO.println s!"Result: max feasible γ ≈ {(lo + hi) / 2} (expected: 10.0)"
  IO.println ""

/-! ## Test 4: Two-Parameter Problem Setup

This demonstrates how to set up a problem with TWO parameters (γ₁, γ₂).
You would use this as a template for your bilinear bisection.

Problem:
  Minimize: x + y
  Subject to:
    γ₁ * x + y >= 1
    x + γ₂ * y >= 1
    x, y >= 0
-/

/-- Two-parameter problem: coefficients depend on (γ₁, γ₂) -/
def twoParamLP (γ₁ γ₂ : Float) : ProblemData :=
  ProblemData.empty
    |>.setObjectiveOnlyVector #[1.0, 1.0] 0.0
    -- γ₁ * x + y >= 1
    |>.addPosOrthConstraint #[γ₁, 1.0] (-1.0)
    -- x + γ₂ * y >= 1
    |>.addPosOrthConstraint #[1.0, γ₂] (-1.0)
    |>.addPosOrthConstraint #[1.0, 0.0] 0.0
    |>.addPosOrthConstraint #[0.0, 1.0] 0.0

def twoParamLPSections : ScalarAffineSections := #[1, 2, 3, 4]

/-- As a ParameterizedProblem with tuple parameter -/
def twoParamLPProblem : ParameterizedProblem (Float × Float) := {
  build := fun (γ₁, γ₂) => twoParamLP γ₁ γ₂
  sections := twoParamLPSections
  totalDim := 2
  description := "Two-parameter LP with bilinear-like structure"
}

/-- Test the two-parameter problem at various (γ₁, γ₂) combinations -/
def testTwoParam : IO Unit := do
  IO.println "=== Test 4: Two-Parameter Problem ==="
  IO.println "Testing feasibility at various (γ₁, γ₂) combinations..."

  let testPoints := [(1.0, 1.0), (2.0, 2.0), (0.5, 0.5), (0.1, 0.1), (5.0, 5.0)]
  for (γ₁, γ₂) in testPoints do
    let feasible ← twoParamLPProblem.isFeasibleAt (γ₁, γ₂)
    let result ← twoParamLPProblem.solveAt (γ₁, γ₂)
    let valStr := match result.varValues? with
      | some [x, y] => s!"x={x}, y={y}"
      | _ => "N/A"
    IO.println s!"  (γ₁={γ₁}, γ₂={γ₂}): feasible={feasible}, {valStr}"
  IO.println ""

/-! ## Main Test Runner -/

/-- Run all tests -/
def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     CvxLean Pure IO Solver Tests - Linear Programs           ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  testSimpleLP
  testParameterizedLP
  testBisection
  testTwoParam

  IO.println "All tests completed!"

-- Uncomment to run tests via #eval:
-- #eval main

end CvxLean.Test.SolveIOLinear
