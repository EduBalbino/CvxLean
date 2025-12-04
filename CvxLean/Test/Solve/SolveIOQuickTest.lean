import CvxLean.Command.Solve.Mosek.SolveIO

/-!
# Quick Test: Pure IO Solver

A minimal test to verify the Pure IO solver works.
Run this file to see solver output.
-/

open CvxLean

/-- Simple LP: minimize x s.t. x >= 1, x >= 0. Optimal x* = 1. -/
def quickTestLP : ProblemData :=
  ProblemData.empty
    |>.setObjectiveOnlyVector #[1.0] 0.0   -- minimize x
    |>.addPosOrthConstraint #[1.0] (-1.0)  -- x >= 1
    |>.addPosOrthConstraint #[1.0] 0.0     -- x >= 0

def quickTestSections : ScalarAffineSections := #[1, 2]

#eval do
  IO.println "Running Pure IO Solver Quick Test..."
  let result ← solveProblemDataIO quickTestLP quickTestSections 1
  match result with
  | .success sol =>
      IO.println s!"✓ Solver succeeded!"
      IO.println s!"  Status: {sol.status}"
      for v in sol.varsSols do
        IO.println s!"  {v.name} = {v.value}"
      if sol.status == "PRIMAL_AND_DUAL_FEASIBLE" then
        IO.println "✓ Problem is feasible, expected x* ≈ 1.0"
      else
        IO.println "⚠ Unexpected status"
  | .cbfError msg => IO.println s!"✗ CBF Error: {msg}"
  | .mosekError code stderr => IO.println s!"✗ MOSEK Error ({code}): {stderr}"
  | .parseError msg => IO.println s!"✗ Parse Error: {msg}"
