import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import CvxLean.Lib.Math.LinearAlgebra.Matrix.PosDef
import CvxLean.Lib.Math.LinearAlgebra.Eigenspace

/-!
If `A` and `B` are positive semi-definite, then `det A + det B ≤ det (A + B)`. This is needed to
define the log-det atom.
-/

namespace Finset

open BigOperators

lemma one_add_prod_le_prod_one_add {n : Type _} [Fintype n] [Nonempty n]
    (f : n → ℝ) (hf : ∀ i, 0 ≤ f i) : 1 + (∏ i, f i) ≤ ∏ i, (1 + f i) := by
  classical
  have key : ∏ i, (1 + f i) = ∑ t : Finset n, ∏ a ∈ univ \ t, f a := by
    rw [prod_add, powerset_univ]
    congr 1
    funext t
    simp
  rw [key]
  have h1 : (1 : ℝ) = ∏ _a ∈ univ \ univ, f _a := by simp
  have h2 : ∏ i, f i = ∏ a ∈ univ \ ∅, f a := by simp
  rw [h1, h2]
  -- Need to show: ∏ ∈ univ \ univ, f + ∏ ∈ univ \ ∅, f ≤ ∑ t, ∏ ∈ univ \ t, f
  -- The LHS is the sum of two specific terms, the RHS is the sum over all t
  have huniv : univ ∈ (univ : Finset (Finset n)) := mem_univ _
  have hempty : ∅ ∈ (univ : Finset (Finset n)) := mem_univ _
  have hne : (univ : Finset n) ≠ ∅ := Finset.univ_nonempty.ne_empty
  calc ∏ _a ∈ univ \ univ, f _a + ∏ a ∈ univ \ ∅, f a
      = ∑ t ∈ ({univ, ∅} : Finset (Finset n)), ∏ a ∈ univ \ t, f a := by
        rw [sum_pair hne]
    _ ≤ ∑ t : Finset n, ∏ a ∈ univ \ t, f a := by
        apply sum_le_univ_sum_of_nonneg
        intro t
        exact prod_nonneg (fun i _ => hf i)

end Finset

namespace Matrix

variable {n : Type _} [Fintype n] [DecidableEq n] [LinearOrder n] [LocallyFiniteOrderBot n]

open BigOperators Matrix

namespace IsHermitian

variable {𝕜 : Type _} [DecidableEq 𝕜] [RCLike 𝕜] {A : Matrix n n 𝕜} (hA : A.IsHermitian)

-- The old `eigenvectorMatrixInv * eigenvectorMatrix = 1` is now via unitary properties.
-- `star (eigenvectorUnitary hA) * eigenvectorUnitary hA = 1`
omit [LinearOrder n] [LocallyFiniteOrderBot n] [DecidableEq 𝕜] in
lemma eigenvectorUnitary_star_mul_self :
    star (hA.eigenvectorUnitary : Matrix n n 𝕜) * hA.eigenvectorUnitary = 1 := by
  exact Unitary.coe_star_mul_self _

omit [LinearOrder n] [LocallyFiniteOrderBot n] [DecidableEq 𝕜] in
lemma eigenvectorUnitary_mul_star_self :
    (hA.eigenvectorUnitary : Matrix n n 𝕜) * star hA.eigenvectorUnitary = 1 := by
  exact Unitary.coe_mul_star_self _

end IsHermitian

-- Define sqrt using the new eigenvectorUnitary API
noncomputable def IsHermitian.sqrt {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  (hA.eigenvectorUnitary : Matrix n n ℝ) *
    Matrix.diagonal (fun i => (hA.eigenvalues i).sqrt) *
    star (hA.eigenvectorUnitary : Matrix n n ℝ)

lemma conjTranspose_eq_transpose {m n : Type _} {A : Matrix m n ℝ} : Aᴴ = Aᵀ := rfl

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
@[simp]
lemma PosSemidef.sqrt_mul_sqrt {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    hA.1.sqrt * hA.1.sqrt = A := by
  unfold IsHermitian.sqrt
  set U := (hA.1.eigenvectorUnitary : Matrix n n ℝ)
  set D := Matrix.diagonal (fun i => (hA.1.eigenvalues i).sqrt)
  have h1 : U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by
    simp only [Matrix.mul_assoc]
  have h2 : star U * U = 1 := Unitary.coe_star_mul_self _
  have h3 : D * D = diagonal (fun i => hA.1.eigenvalues i) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Real.sqrt_mul (hA.eigenvalues_nonneg i), Real.sqrt_mul_self (hA.eigenvalues_nonneg i)]
  calc U * D * star U * (U * D * star U)
      = U * D * (star U * U) * D * star U := h1
    _ = U * D * 1 * D * star U := by rw [h2]
    _ = U * D * D * star U := by rw [Matrix.mul_one]
    _ = U * (D * D) * star U := by simp only [Matrix.mul_assoc]
    _ = U * diagonal (fun i => hA.1.eigenvalues i) * star U := by rw [h3]
    _ = U * diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) * star U := by simp
    _ = A := hA.1.spectral_theorem.symm

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
lemma PosSemidef.PosSemidef_sqrt {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    hA.1.sqrt.PosSemidef := by
  unfold IsHermitian.sqrt
  -- U * D * star U where D is diagonal with nonneg entries
  -- This is (star U)ᴴ * D * star U = U * D * star U
  have hD : (Matrix.diagonal (fun i => (hA.1.eigenvalues i).sqrt)).PosSemidef :=
    PosSemidef.diagonal (fun i => Real.sqrt_nonneg (hA.1.eigenvalues i))
  exact hD.mul_mul_conjTranspose_same _

omit [Fintype n] [LinearOrder n] [LocallyFiniteOrderBot n] in
lemma IsHermitian.one_add {A : Matrix n n ℝ} (hA : A.IsHermitian) : (1 + A).IsHermitian := by
  dsimp [IsHermitian]; rw [IsHermitian.add _ hA]; simp

-- The old `has_eigenvector_one_add` used the old eigenvector API.
-- In the new API, we use `mulVec_eigenvectorBasis` instead.
omit [LinearOrder n] [LocallyFiniteOrderBot n] in
lemma IsHermitian.has_eigenvector_one_add {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    (1 + A) *ᵥ ⇑(hA.eigenvectorBasis i) = (1 + hA.eigenvalues i) • ⇑(hA.eigenvectorBasis i) := by
  rw [add_mulVec, one_mulVec, hA.mulVec_eigenvectorBasis, add_smul, one_smul]

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
/-- The determinant of `1 + A` equals the product of `1 + eigenvalues` for a Hermitian matrix. -/
lemma IsHermitian.det_one_add_eq_prod_one_add_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (1 + A).det = ∏ i, (1 + hA.eigenvalues i) := by
  set U := (hA.eigenvectorUnitary : Matrix n n ℝ)
  set D := diagonal ((RCLike.ofReal (K := ℝ)) ∘ hA.eigenvalues)
  have hU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hU' : star U * U = 1 := Unitary.coe_star_mul_self _
  have hspec : A = U * D * star U := hA.spectral_theorem
  have h1 : 1 + A = U * (1 + D) * star U := by
    calc 1 + A = 1 + U * D * star U := by rw [hspec]
      _ = U * star U + U * D * star U := by rw [hU]
      _ = U * 1 * star U + U * D * star U := by simp only [Matrix.mul_one]
      _ = (U * 1 + U * D) * star U := by rw [Matrix.add_mul]
      _ = U * (1 + D) * star U := by rw [← Matrix.mul_add, Matrix.mul_assoc]
  have h2 : 1 + D = diagonal (fun i => 1 + hA.eigenvalues i) := by
    rw [← diagonal_one, diagonal_add]
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  rw [h1, h2, det_mul, det_mul, det_diagonal]
  have hdet : (star U).det * U.det = 1 := by rw [← det_mul, hU', det_one]
  calc (U.det * ∏ i, (1 + hA.eigenvalues i)) * (star U).det
      = U.det * (∏ i, (1 + hA.eigenvalues i)) * (star U).det := by ring
    _ = (∏ i, (1 + hA.eigenvalues i)) * (U.det * (star U).det) := by ring
    _ = (∏ i, (1 + hA.eigenvalues i)) * ((star U).det * U.det) := by ring
    _ = (∏ i, (1 + hA.eigenvalues i)) * 1 := by rw [hdet]
    _ = ∏ i, (1 + hA.eigenvalues i) := by ring

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
lemma PosDef.PosDef_sqrt {A : Matrix n n ℝ} (hA : A.PosDef) : hA.1.sqrt.PosDef := by
  unfold IsHermitian.sqrt
  set U := (hA.1.eigenvectorUnitary : Matrix n n ℝ)
  have hD : (Matrix.diagonal (fun i => (hA.1.eigenvalues i).sqrt)).PosDef :=
    PosDef.diagonal (fun i => Real.sqrt_pos.2 (hA.eigenvalues_pos i))
  have hU_isUnit : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hmem := hA.1.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff] at hmem
    have hdet : U.det * (star U).det = 1 := by
      rw [← det_mul, hmem, det_one]
    exact IsUnit.of_mul_eq_one _ hdet
  have hU_inj : Function.Injective U.vecMul := vecMul_injective_of_isUnit hU_isUnit
  exact hD.mul_mul_conjTranspose_same hU_inj

omit [DecidableEq n] [LinearOrder n] [LocallyFiniteOrderBot n] in
lemma PosSemidef.PosDef_iff_det_ne_zero [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    M.PosDef ↔ M.det ≠ 0 := by
  constructor
  · intro h
    exact h.det_pos.ne'
  · intro hdet
    constructor
    · exact hM.1
    · intros x hx
      apply lt_of_le_of_ne' (hM.2 x)
      rw [← hM.sqrt_mul_sqrt, ← mulVec_mulVec, dotProduct_mulVec, ← transpose_transpose hM.1.sqrt,
        vecMul_transpose, transpose_transpose, ← conjTranspose_eq_transpose,
        hM.PosSemidef_sqrt.1.eq]
      simp only [star, id]
      intro h0
      have hzero : hM.1.sqrt.mulVec x = 0 := dotProduct_self_eq_zero.mp h0
      have sqrtMdet0 : hM.1.sqrt.det = 0 := by
        refine exists_mulVec_eq_zero_iff.1 ⟨x, hx, hzero⟩
      rw [← hM.sqrt_mul_sqrt, det_mul, sqrtMdet0, mul_zero] at hdet
      exact hdet rfl

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
/-- Subadditivity lemma for positive semidefinite matrices. This version assumes that one of the
matrices is positive definite. See `det_add_det_le_det_add` for the more general statement.

The argument is taken from Andreas Thom's comment on mathoverflow:
https://mathoverflow.net/questions/65424/determinant-of-sum-of-positive-definite-matrices. -/
lemma det_add_det_le_det_add' [Nonempty n] (A B : Matrix n n ℝ) (hA : A.PosDef)
    (hB : B.PosSemidef) : A.det + B.det ≤ (A + B).det := by
  let sqrtA := hA.1.sqrt
  have isUnit_det_sqrtA :=
    isUnit_iff_ne_zero.2 hA.PosDef_sqrt.det_pos.ne'
  have : IsUnit sqrtA :=
    (isUnit_iff_isUnit_det _).2 isUnit_det_sqrtA
  have IsHermitian_sqrtA : sqrtA⁻¹.IsHermitian := by
  { apply IsHermitian.nonsingular_inv (hA.posSemidef.PosSemidef_sqrt.1)
    exact isUnit_det_sqrtA }
  have PosSemidef_ABA : (sqrtA⁻¹ * B * sqrtA⁻¹).PosSemidef := by
    rw [show sqrtA⁻¹ * B * sqrtA⁻¹ = sqrtA⁻¹ᴴ *  B * sqrtA⁻¹ from by rw [IsHermitian_sqrtA.eq]]
    exact hB.conjTranspose_mul_mul_same sqrtA⁻¹
  let μ := PosSemidef_ABA.1.eigenvalues
  calc A.det + B.det
    = A.det * (1 + (sqrtA⁻¹ * B * sqrtA⁻¹).det) := by
        rw [det_mul, det_mul, mul_comm _ B.det, mul_assoc, ← det_mul, ← Matrix.mul_inv_rev,
          hA.posSemidef.sqrt_mul_sqrt, mul_add, mul_one, mul_comm, mul_assoc, ← det_mul,
          nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA.det_pos.ne'), det_one, mul_one]
  _ = A.det * (1 + ∏ i, μ i) := by
        rw [PosSemidef_ABA.1.det_eq_prod_eigenvalues]
        rfl
  _ ≤ A.det * ∏ i, (1 + μ i) := by
        apply (mul_le_mul_iff_right₀ hA.det_pos).2
        apply Finset.one_add_prod_le_prod_one_add μ PosSemidef_ABA.eigenvalues_nonneg
  _ = A.det * (1 + sqrtA⁻¹ * B * sqrtA⁻¹).det := by
        rw [mul_eq_mul_left_iff]; left; symm
        exact PosSemidef_ABA.1.det_one_add_eq_prod_one_add_eigenvalues
  _ = (A + B).det := by
        rw [← det_mul, ← det_conj this (A + B)]
        apply congr_arg
        rw [← hA.posSemidef.sqrt_mul_sqrt]
        change sqrtA * sqrtA * (1 + sqrtA⁻¹ * B * sqrtA⁻¹) = sqrtA * (sqrtA * sqrtA + B) * sqrtA⁻¹
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ _ (B * _),
          Matrix.mul_nonsing_inv _ isUnit_det_sqrtA, Matrix.one_mul, Matrix.mul_one,
          hA.posSemidef.sqrt_mul_sqrt, Matrix.mul_assoc]

omit [LinearOrder n] [LocallyFiniteOrderBot n] in
/-- Subadditivity lemma for positive semidefinite matrices. -/
lemma det_add_det_le_det_add [Nonempty n] (A B : Matrix n n ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) : A.det + B.det ≤ (A + B).det := by
  by_cases hA' : A.det = 0
  { by_cases hB' : B.det = 0
    { simp [hA', hB']
      apply (hA.add hB).det_nonneg }
    { rw [add_comm A B, add_comm A.det B.det]
      apply det_add_det_le_det_add' _ _ (hB.PosDef_iff_det_ne_zero.2 hB') hA } }
  { apply det_add_det_le_det_add' _ _ (hA.PosDef_iff_det_ne_zero.2 hA') hB }

end Matrix
