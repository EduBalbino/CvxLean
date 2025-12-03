import CvxLean.Command.Solve

/-!
# Testing the PosDef atom

These tests verify that `Matrix.PosDef` works as a direct DCP constraint.
-/

section PosDef

open CvxLean Minimization Real

/-- Test 1: Minimize trace(X) subject to X ≻ 0 and X_00 ≥ 1. -/
noncomputable def posDef1 :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize (Matrix.trace X)
    subject to
      h_pd : X.PosDef
      h_bound : 1 ≤ X 0 0

solve posDef1

#eval posDef1.status
#eval posDef1.value
#eval posDef1.solution 0 0
#eval posDef1.solution 0 1
#eval posDef1.solution 1 0
#eval posDef1.solution 1 1

/-- Test 2: Maximize trace(X) subject to X ≻ 0 and diagonal entries ≤ 10. -/
noncomputable def posDef2 :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    maximize (Matrix.trace X)
    subject to
      h_pd : X.PosDef
      h_bound1 : X 0 0 ≤ 10
      h_bound2 : X 1 1 ≤ 10

solve posDef2

#eval posDef2.status
#eval posDef2.value
#eval posDef2.solution 0 0
#eval posDef2.solution 0 1
#eval posDef2.solution 1 0
#eval posDef2.solution 1 1

/-- Test 3: 3x3 PosDef problem. Minimize diagonal sum subject to X ≻ 0 and sum ≥ 3. -/
noncomputable def posDef3 :=
  optimization (X : Matrix (Fin 3) (Fin 3) ℝ)
    minimize (X 0 0 + X 1 1 + X 2 2)
    subject to
      h_pd : X.PosDef
      h_sum : 3 ≤ X 0 0 + X 1 1 + X 2 2

solve posDef3

#eval posDef3.status
#eval posDef3.value
#eval posDef3.solution 0 0
#eval posDef3.solution 1 1
#eval posDef3.solution 2 2

/-- Test 4: PosDef with off-diagonal constraint. -/
noncomputable def posDef4 :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize (Matrix.trace X)
    subject to
      h_pd : X.PosDef
      h_diag : 2 ≤ X 0 0
      h_sym1 : X 0 1 = 1
      h_sym2 : X 1 0 = 1

solve posDef4

#eval posDef4.status
#eval posDef4.value
#eval posDef4.solution 0 0
#eval posDef4.solution 0 1
#eval posDef4.solution 1 0
#eval posDef4.solution 1 1

/-- Test 5: Comparison with PosSemidef (allows boundary solutions). -/
noncomputable def posSemidef_comparison :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize (Matrix.trace X)
    subject to
      h_psd : X.PosSemidef
      h_bound : 1 ≤ X 0 0

solve posSemidef_comparison

#eval posSemidef_comparison.status
#eval posSemidef_comparison.value
#eval posSemidef_comparison.solution 0 0
#eval posSemidef_comparison.solution 1 1

end PosDef
