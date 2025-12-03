import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
More results about positive definite and positive semidefinite matrices (see
`Mathlib.LinearAlgebra.Matrix.PosDef`).

Note: Many lemmas that were previously here have been upstreamed to Mathlib.
This file now contains only supplementary results.
-/

namespace CvxLean

/-! ## PosDef Atom Configuration -/

/-- Exponent for PosDef epsilon: ε = 10^(-n). Default: 8. -/
register_option posDef.epsilonExp : Nat := {
  defValue := 8
  descr := "Exponent n for PosDef epsilon: ε = 10^(-n)"
}

/-- The epsilon value for PosDef relaxation. -/
def posDef.epsilon : ℝ := 1e-8

/-- Proof that epsilon is positive. -/
lemma posDef.epsilon_pos : 0 < posDef.epsilon := by
  unfold posDef.epsilon
  norm_num

end CvxLean

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]

-- PosSemidef.det_nonneg is now in Mathlib.Analysis.Matrix.PosDef
-- PosDef.det_ne_zero is now in Mathlib (via PosDef.isUnit)

lemma PosDef.isUnit_det' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) : IsUnit M.det :=
  isUnit_iff_isUnit_det M |>.mp hM.isUnit

-- PosSemidef.diagonal is now in Mathlib
-- PosDef.diagonal is now in Mathlib

-- PosSemidef.conjTranspose_mul_mul_same is now in Mathlib
-- PosDef.conjTranspose_mul_mul_same is now in Mathlib

lemma IsHermitian.nonsingular_inv [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.IsHermitian)
    (hMdet : IsUnit M.det) : M⁻¹.IsHermitian := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [conjTranspose_nonsing_inv, hM.eq, mul_nonsing_inv _ hMdet]

lemma conj_symm [DecidableEq n] {x : n → 𝕜} {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    star (star x ⬝ᵥ mulVec M x) = star x ⬝ᵥ mulVec M x := by
  nth_rewrite 1 [star_dotProduct, star_mulVec]
  rw [star_star, dotProduct_mulVec, hM.eq]

-- PosDef.inv is now in Mathlib
-- PosSemidef.add is now in Mathlib (as PosSemidef.add with [AddLeftMono R])

lemma isUnit_det_of_PosDef_inv [DecidableEq n] {M : Matrix n n ℝ} (h : M⁻¹.PosDef) :
    IsUnit M.det := by
  have hU := isUnit_iff_isUnit_det _ |>.mp h.isUnit
  rw [det_nonsing_inv, isUnit_ringInverse] at hU
  exact hU.ne_zero |> isUnit_iff_ne_zero.mpr

-- PosDef_inv_iff_PosDef is now Matrix.posDef_inv_iff in Mathlib

lemma PosSemiDef.IsSymm {n} {A : Matrix (Fin n) (Fin n) ℝ} (hA : PosSemidef A) : IsSymm A := by
  apply IsSymm.ext
  intros i j
  have hH := hA.isHermitian
  simp only [IsHermitian, conjTranspose] at hH
  have := congrFun (congrFun hH i) j
  simp only [transpose_apply, map_apply, star_trivial] at this
  exact this

/-! ## PosDef ↔ PosSemidef relaxation -/

/-- If `(A - ε • 1).PosSemidef` for some `ε > 0`, then `A.PosDef`. -/
lemma PosDef_of_PosSemidef_sub_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} {ε : ℝ} (hε : 0 < ε) (hA : (A - ε • (1 : Matrix n n ℝ)).PosSemidef) :
    A.PosDef := by
  have hAH : A.IsHermitian := by
    have h := hA.isHermitian
    simp only [IsHermitian, conjTranspose_sub, conjTranspose_smul,
      conjTranspose_one, star_trivial] at h ⊢
    exact sub_left_injective h
  refine ⟨hAH, fun x hx => ?_⟩
  have key : star x ⬝ᵥ mulVec A x =
      star x ⬝ᵥ mulVec (A - ε • 1) x + ε * (star x ⬝ᵥ x) := by
    simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, star_trivial,
      smul_eq_mul]
    ring
  rw [key]
  have h1 : 0 ≤ star x ⬝ᵥ mulVec (A - ε • 1) x := hA.2 x
  have h2 : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.mpr hx
  linarith [mul_pos hε h2]

end Matrix
