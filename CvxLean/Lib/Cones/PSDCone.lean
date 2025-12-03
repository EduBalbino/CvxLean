import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Positive semidefinite cone and positive definite cone (ε-relaxation).
-/

namespace Real

/-- The cone of `n×n` positive semidefinite matrices
      `𝒮₊ⁿ := { A | A is symmetric ∧ 0 ≼ A } ⊆ ℝⁿˣⁿ`. -/
def Matrix.PSDCone {n} [Fintype n] (A : Matrix n n ℝ) : Prop :=
  Matrix.PosSemidef A

/-- The ε-interior of the PSD cone, representing matrices with eigenvalues ≥ ε.
This is used for `Matrix.PosDef` constraints: `(A - ε•I) ≽ 0` implies `A ≻ 0`.

The cone constraint `PSDConeShifted ε A` sends `(A - ε•I) ≽ 0` to the solver,
which enforces `λ_min(A) ≥ ε > 0`, guaranteeing positive definiteness. -/
def Matrix.PSDConeShifted {n} [Fintype n] [DecidableEq n] (ε : ℝ) (A : Matrix n n ℝ) : Prop :=
  Matrix.PosSemidef (A - ε • (1 : Matrix n n ℝ))

end Real
