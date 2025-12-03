import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

/-!
Second-order cones.

We follow the MOSEK modeling cookbook: https://docs.mosek.com/modeling-cookbook/cqo.html
-/

namespace Real

open BigOperators

variable {n m} [Fintype m] [Fintype n]

/-- The `n`-dimensional second-order cone
      `𝒬ⁿ⁺¹ := { (t, x) | ‖x‖₂ = sqrt(x₁² + ⋯ + xₙ²) ≤ t } ⊆ ℝ × ℝⁿ`. -/
def soCone (t : ℝ) (x : n → ℝ) : Prop :=
  sqrt (∑ i, x i ^ 2) ≤ t

/-- `soCone t x` is equivalent to `l2Norm x ≤ t` for `Fin n → ℝ`. -/
lemma soCone_iff_l2Norm_le {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    soCone t x ↔ Vec.l2Norm x ≤ t := by
  unfold soCone Vec.l2Norm
  rw [EuclideanSpace.norm_eq]
  simp only [norm_eq_abs, sq_abs, rpow_two]

/-- The `n`-dimensional rotated second-order cone
      `𝒬ᵣⁿ⁺² := { (v, w, x) | x₁² + ⋯ + xₙ² ≤ 2vw ∧ 0 ≤ v, w } ⊆ ℝ × ℝ × ℝⁿ`. -/
def rotatedSoCone (v w : ℝ) (x : n → ℝ) : Prop :=
  (∑ i, x i ^ 2) ≤ (v * w) * 2 ∧ 0 ≤ v ∧ 0 ≤ w

/-- `m` copies of the `n`-dimensional second-order cone `(𝒬ⁿ)ᵐ`. -/
def Vec.soCone (t : m → ℝ) (X : Matrix m n ℝ) : Prop :=
  ∀ i, Real.soCone (t i) (X i)

/-- `m` copies of the `n`-dimensional rotated second-order cone `(𝒬ᵣⁿ)ᵐ`. -/
def Vec.rotatedSoCone (v w : m → ℝ) (X : Matrix m n ℝ) : Prop :=
  ∀ i, Real.rotatedSoCone (v i) (w i) (X i)

noncomputable section ConeConversion

/-- If `(t, x) ∈ 𝒬ⁿ⁺¹` then `r(t, x) ∈ 𝒬ᵣⁿ⁺²`. -/
def rotateSoCone {n : ℕ} (t : ℝ) (x : Fin n.succ → ℝ) : ℝ × ℝ × (Fin n → ℝ) :=
  ((t + x 0) / sqrt 2, (t - x 0) / sqrt 2, fun i => x i.succ)

lemma rotateSoCone_rotatedSoCone {n : ℕ} {t : ℝ} {x : Fin n.succ → ℝ} (h : soCone t x) :
    let (v, w, x) := rotateSoCone t x; rotatedSoCone v w x := by
  simp [rotatedSoCone, rotateSoCone]
  have habsx0t : |x 0| ≤ t := by
    rw [soCone, Fin.sum_univ_succ] at h
    have hS : 0 ≤ ∑ i : Fin n, x (Fin.succ i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => (rpow_two (x i.succ)).symm ▸ sq_nonneg (x i.succ))
    exact abs_le_of_sqrt_sq_add_nonneg_le hS h
  have ht : 0 ≤ t := le_trans (abs_nonneg _) habsx0t
  replace ⟨hx0t, hnx0t⟩ := abs_le.mp habsx0t
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    -- Goal: (∑ x_1, x x_1.succ ^ 2) * √2 ^ 2 ≤ (t + x 0) * (t - x 0) * 2
    -- Convert all ^ 2 to natural power using rpow_two
    simp only [← rpow_two] at *
    -- Now use the original proof structure
    have hrw : (t + x 0) * (t - x 0) = t ^ (2:ℕ) - x 0 ^ (2:ℕ) := by ring
    simp only [rpow_two]
    rw [hrw]
    unfold soCone at h
    rw [Fin.sum_univ_succ] at h
    have h1 : 0 ≤ ∑ i : Fin n, x i.succ ^ (2:ℕ) := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hsqrt2 : (√2 : ℝ) ^ (2:ℕ) = 2 := sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
    simp only [← rpow_two] at h1
    simp only [rpow_two] at h
    have hsum_sq : x 0 ^ (2:ℕ) + ∑ i : Fin n, x i.succ ^ (2:ℕ) ≤ t ^ (2:ℕ) := by
      -- Use sqrt_le_left: √x ≤ y ↔ x ≤ y ^ 2
      rw [Real.sqrt_le_left ht] at h
      exact h
    -- Now: need (∑ i, x i.succ ^ 2) * √2 ^ 2 ≤ (t ^ 2 - x 0 ^ 2) * 2
    -- We have: ∑ i, x i.succ ^ 2 ≤ t ^ 2 - x 0 ^ 2 (from hsum_sq)
    -- And: √2 ^ 2 = 2 (from hsqrt2)
    have hle : ∑ i : Fin n, x i.succ ^ (2:ℕ) ≤ t ^ (2:ℕ) - x 0 ^ (2:ℕ) := by linarith
    calc (∑ i : Fin n, x i.succ ^ (2:ℕ)) * √2 ^ (2:ℕ)
        = (∑ i : Fin n, x i.succ ^ (2:ℕ)) * 2 := by rw [hsqrt2]
      _ ≤ (t ^ (2:ℕ) - x 0 ^ (2:ℕ)) * 2 := by linarith
  · have h2pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    rw [le_div_iff₀ h2pos]; linarith
  · have h2pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    rw [le_div_iff₀ h2pos]; linarith

/-- If `(v, w, x) ∈ 𝒬ⁿ⁺²` then `u(v, w, x) ∈ 𝒬ᵣⁿ⁺¹`. -/
def unrotateSoCone {n : ℕ} (v w : Real) (x : Fin n → ℝ) : ℝ × (Fin n.succ → ℝ) :=
  ((v + w) / sqrt 2, Matrix.vecCons ((v - w) / sqrt 2) x)

lemma unrotateSoCone_soCone {n : ℕ} {v w : ℝ} {x : Fin n → ℝ} (h : rotatedSoCone v w x) :
    let (t, x) := unrotateSoCone v w x; soCone t x := by
  simp [soCone, unrotateSoCone]
  replace ⟨h, hv, hw⟩ := h
  rw [sqrt_le_iff]
  refine ⟨?_, ?_⟩
  · have h2pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    rw [le_div_iff₀ h2pos]; linarith
  · rw [Fin.sum_univ_succ]
    simp only [Matrix.vecCons, Fin.cons_zero, Fin.cons_succ]
    -- Convert real powers to natural powers
    simp only [rpow_two] at h ⊢
    have hsqrt2 : (√2 : ℝ) ^ (2 : ℕ) = 2 := sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
    -- Key identity: (v+w)² - (v-w)² = 4vw
    have hrw : (v + w) ^ (2:ℕ) - (v - w) ^ (2:ℕ) = v * w * 4 := by ring
    -- Goal: ((v-w)/√2)² + ∑ x_i² ≤ ((v+w)/√2)²
    -- i.e., ∑ x_i² ≤ ((v+w)² - (v-w)²) / 2 = 2vw
    have hdiv : ((v + w) / √2) ^ (2:ℕ) - ((v - w) / √2) ^ (2:ℕ) = v * w * 2 := by
      field_simp
      rw [hsqrt2, hrw]
      ring
    linarith

end ConeConversion

section Lemmas

/-- To handle powers, a common trick is to use the fact that for
`x, y ≥ 0` and `z ∈ ℝ`,
      `((x + y), (x - y, 2z)ᵀ) ∈ 𝒬ⁿ⁺¹ ↔ z ^ 2 ≤ xy`. -/
lemma soCone_add_sub_two_mul_of_nonneg {x y : ℝ} (z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : soCone (x + y) ![x - y, 2 * z] ↔ z ^ (2 : ℝ) ≤ x * y := by
  have hxy := add_nonneg hx hy
  conv => lhs; unfold soCone; simp [sqrt_le_left hxy, ← le_sub_iff_add_le']
  ring_nf; simp

/-- Same as `soCone_add_sub_two_mul_of_nonneg` with `z = 1`. -/
lemma soCone_add_sub_two_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    soCone (x + y) ![x - y, 2] ↔ 1 ≤ x * y := by
  have h := soCone_add_sub_two_mul_of_nonneg 1 hx hy
  rw [mul_one, one_rpow] at h
  exact h

/-- Same as `soCone_add_sub_two_mul_of_nonneg` replacing `y` by `-y`. -/
lemma soCone_sub_add_two_mul_of_nonneg {x y : ℝ} (z : ℝ) :
    soCone (x - y) ![x + y, 2 * z] ↔ y ≤ x ∧ z ^ (2 : ℝ) ≤ -(x * y) := by
  conv => lhs; unfold soCone; simp [sqrt_le_iff, ← le_sub_iff_add_le']
  apply Iff.and
  · rfl
  · simp only [rpow_two]
    constructor <;> intro h <;> nlinarith [sq_nonneg z, sq_nonneg (x + y), sq_nonneg (x - y)]

open Real Matrix

lemma vec_soCone_apply_to_soCone_add_sub_two_mul {n : ℕ} (x y z : Fin n → ℝ) (i : Fin n) :
    (soCone ((x + y) i) ((![x - y, 2 • z]ᵀ) i)) ↔ (soCone (x i + y i) ![x i - y i, 2 * z i]) := by
  dsimp; convert Iff.rfl; funext j; fin_cases j <;> simp

lemma vec_soCone_apply_to_soCone_add_sub_two {n : ℕ} (x y : Fin n → ℝ) (i : Fin n) :
    (soCone ((x + y) i) ((![x - y, 2]ᵀ) i)) ↔ (soCone (x i + y i) ![x i - y i, 2]) := by
  dsimp; convert Iff.rfl; funext j; fin_cases j <;> simp

end Lemmas

end Real
