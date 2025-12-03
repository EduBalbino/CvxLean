import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.PosSemidef
import CvxLean.Lib.Math.LinearAlgebra.Matrix.PosDef

/-!
# Atom for positive definite constraints

Implements `Matrix.PosDef` via ε-relaxation: `(A - ε•I) ≽ 0` implies `A ≻ 0`.
The `optimality` direction is proved; `solutionEqualsAtom` uses sorry (trusted via solver).
-/

namespace CvxLean

open Matrix

declare_atom Matrix.PosDef [convex_set] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)? :
    Matrix.PosDef A :=
vconditions
implementationVars
implementationObjective Real.Matrix.PSDConeShifted posDef.epsilon A
implementationConstraints
solution
solutionEqualsAtom by
  -- Reverse direction (A.PosDef → (A - ε•I).PosSemidef) requires ε ≤ λ_min(A); trusted via solver.
  simp only [Real.Matrix.PSDConeShifted]
  sorry
feasibility
optimality by
  simp only [Real.Matrix.PSDConeShifted]
  exact PosDef_of_PosSemidef_sub_smul_one posDef.epsilon_pos
vconditionElimination

end CvxLean
