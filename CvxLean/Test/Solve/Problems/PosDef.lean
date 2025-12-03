import CvxLean.Command.Solve

/-!
# Testing the PosDef atom

These tests verify that `Matrix.PosDef` works as a direct DCP constraint.
-/

section PosDef

open CvxLean Minimization Real

/-- Test 1: Simple problem with PosDef constraint.
Minimize trace(X) subject to X ≻ 0 and X_00 ≥ 1.
Expected: X = [[1, 0], [0, ε]] for small ε. -/
noncomputable def posDef1 :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize (Matrix.trace X)
    subject to
      h_pd : X.PosDef
      h_bound : 1 ≤ X 0 0

solve posDef1

#eval posDef1.status       -- Should be "PRIMAL_AND_DUAL_FEASIBLE"
#eval posDef1.value        -- Should be close to 1 (or slightly more)
#eval posDef1.solution 0 0 -- Should be 1
#eval posDef1.solution 0 1 -- Should be ~0
#eval posDef1.solution 1 0 -- Should be ~0
#eval posDef1.solution 1 1 -- Should be small positive

/-- Test 2: PosDef with trace bound.
Maximize trace(X) subject to X ≻ 0 and all diagonal entries ≤ 10. -/
noncomputable def posDef2 :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    maximize (Matrix.trace X)
    subject to
      h_pd : X.PosDef
      h_bound1 : X 0 0 ≤ 10
      h_bound2 : X 1 1 ≤ 10

solve posDef2

#eval posDef2.status       -- Should be "PRIMAL_AND_DUAL_FEASIBLE"
#eval posDef2.value        -- Should be 20
#eval posDef2.solution 0 0 -- Should be 10
#eval posDef2.solution 1 1 -- Should be 10

/-- Test 3: 3x3 PosDef problem.
Minimize sum of diagonal subject to X ≻ 0 and X_00 + X_11 + X_22 ≥ 3. -/
noncomputable def posDef3 :=
  optimization (X : Matrix (Fin 3) (Fin 3) ℝ)
    minimize (X 0 0 + X 1 1 + X 2 2)
    subject to
      h_pd : X.PosDef
      h_sum : 3 ≤ X 0 0 + X 1 1 + X 2 2

solve posDef3

#eval posDef3.status       -- Should be "PRIMAL_AND_DUAL_FEASIBLE"
#eval posDef3.value        -- Should be 3
#eval posDef3.solution 0 0 -- Should be 1
#eval posDef3.solution 1 1 -- Should be 1
#eval posDef3.solution 2 2 -- Should be 1

end PosDef
