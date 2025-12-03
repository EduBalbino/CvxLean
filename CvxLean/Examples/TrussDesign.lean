import CvxLean

/-!
# Case study: Truss design

See section 6.3 in https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf.
-/

noncomputable section

namespace TrussDesign

open CvxLean Minimization Real

-- Height range (distance between the upper bearing's `y` coordinate and the joint's `y` coordinate;
-- which is the same as the distance from the lower bearing's `y` coordinate, as the truss is
-- assumed to be symmetric along the joint's `x` line).
variable (hmin hmax : ℝ)
variable (hmin_pos : 0 < hmin) (hmin_le_hmax : hmin ≤ hmax)

-- Width range (distance between the bearings' `x` coordinate and the joint's `x` coordinate).
variable (wmin wmax : ℝ)
variable (wmin_pos : 0 < wmin) (wmin_le_wmax : wmin ≤ wmax)

-- Maximum outer radius of the bar.
variable (Rmax : ℝ)

-- Maximum allowable stress.
variable (σ : ℝ)

-- Vertical downward force on the joint.
variable (F₁ : ℝ)

-- Horizontal left-to-right force on the joint.
variable (F₂ : ℝ)

def trussDesign :=
  optimization (h w r R : ℝ) with A := 2 * π * (R ^ 2 - r ^ 2)
    minimize 2 * A * sqrt (w ^ 2 + h ^ 2)
    subject to
      c_r    : 0 < r
      c_F₁   : F₁ * sqrt (w ^ 2 + h ^ 2) / (2 * h) ≤ σ * A
      c_F₂   : F₂ * sqrt (w ^ 2 + h ^ 2) / (2 * w) ≤ σ * A
      c_hmin : hmin ≤ h
      c_hmax : h ≤ hmax
      c_wmin : wmin ≤ w
      c_wmax : w ≤ wmax
      c_R_lb : 1.1 * r ≤ R
      c_R_ub : R ≤ Rmax

instance : ChangeOfVariables
    fun ((h, w, r, A) : ℝ × ℝ × ℝ × ℝ) => (h, w, r, sqrt (A / (2 * π) + r ^ 2)) :=
  { inv := fun (h, w, r, R) => (h, w, r, 2 * π * (R ^ 2 - r ^ 2)),
    condition := fun (_, _, _, R) => 0 ≤ R,
    property := fun (h, w, r, R) hR => by
      simp only at hR
      simp only [mul_comm (2 * π) _, mul_div_assoc, div_self (by positivity : (2 : ℝ) * π ≠ 0),
        mul_one, sub_add_cancel, Prod.mk.injEq, true_and, rpow_two]
      exact sqrt_sq hR }

equivalence* eqv₁/trussDesignGP (hmin hmax wmin wmax Rmax σ F₁ F₂ : ℝ) :
    trussDesign hmin hmax wmin wmax Rmax σ F₁ F₂ := by
  -- Apply key change of variables.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence
      (fun (hwrA : ℝ × ℝ × ℝ × ℝ) =>
        (hwrA.1, hwrA.2.1, hwrA.2.2.1, sqrt (hwrA.2.2.2 / (2 * π) + hwrA.2.2.1 ^ 2)))
    · rintro ⟨h, w, r, R⟩ ⟨c_r, _, _, _, _, _, _, c_R_lb, _⟩; dsimp at *
      simp [ChangeOfVariables.condition]
      have h_r_le : r ≤ 1.1 * r := (le_mul_iff_one_le_left c_r).mpr (by norm_num)
      exact le_trans (le_of_lt c_r) (le_trans h_r_le c_R_lb)
  rename_vars [h, w, r, A]
  -- Some cleanup.
  conv_opt => dsimp
  -- Rewrite contraint `c_R_lb`.
  rw_constr c_R_lb into (0.21 * r ^ 2 ≤ A / (2 * π)) =>
    rw [le_sqrt' (by positivity), rpow_two, mul_pow, ← sub_le_iff_le_add]
    rw [iff_eq_eq]; congr; ring_nf
  -- Useful fact about constraints used for simplification. This is a good example of introducing
  -- local lemmas in an `equivalence` environment.
  have h_A_div_2π_add_r2_nonneg : ∀ (r A : ℝ) (c_r : 0 < r)
    (c_R_lb : 0.21 * r ^ 2 ≤ A / (2 * π)), 0 ≤ A / (2 * π) + r ^ 2 :=
    fun r A c_r c_R_lb => by
      have h_A_div_2π_nonneg : 0 ≤ A / (2 * π) := le_trans (by positivity) c_R_lb
      exact add_nonneg (h_A_div_2π_nonneg) (by positivity)
  -- Simplify objective function.
  rw_obj into (2 * A * sqrt (w ^ 2 + h ^ 2)) =>
    rw [rpow_two, sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
    ring_nf; field_simp
  -- Simplify constraint `c_F₁`.
  rw_constr c_F₁ into (F₁ * sqrt (w ^ 2 + h ^ 2) / (2 * h) ≤ σ * A) =>
    rw [rpow_two (sqrt (_ + r ^ 2)), sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
    rw [iff_eq_eq]; congr; ring_nf; field_simp
  -- Simplify constraint `c_F₂`.
  rw_constr c_F₂ into (F₂ * sqrt (w ^ 2 + h ^ 2) / (2 * w) ≤ σ * A) =>
    rw [rpow_two (sqrt (_ + r ^ 2)), sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
    rw [iff_eq_eq]; congr; ring_nf; field_simp

#print trussDesignGP
-- minimize 2 * A * sqrt (w ^ 2 + h ^ 2)
--   subject to
--     c_r : 0 < r
--     c_F₁ : F₁ * sqrt (w ^ 2 + h ^ 2) / (2 * h) ≤ σ * A
--     c_F₂ : F₂ * sqrt (w ^ 2 + h ^ 2) / (2 * w) ≤ σ * A
--     c_hmin : hmin ≤ h
--     c_hmax : h ≤ hmax
--     c_wmin : wmin ≤ w
--     c_wmax : w ≤ wmax
--     c_A_lb : 0.21 * r ^ 2 ≤ A / (2 * π)
--     c_A_ub : sqrt (A / (2 * π) + r ^ 2) ≤ Rmax

instance : ChangeOfVariables
    fun ((h', w', r', A') : ℝ × ℝ × ℝ × ℝ) => (exp h', exp w', exp r', exp A') :=
  { inv := fun (h, w, r, A) => (log h, log w, log r, log A),
    condition := fun (h', w', r', A') => 0 < h' ∧ 0 < w' ∧ 0 < r' ∧ 0 < A',
    property := fun (h', w', r', A') ⟨hh', hw', hr', hA'⟩ => by
      simp [exp_log hh', exp_log hw', exp_log hr', exp_log hA'] }

equivalence* eqv₂/trussDesignConvex (hmin hmax : ℝ) (hmin_pos : 0 < hmin)
    (_hmin_le_hmax : hmin ≤ hmax) (wmin wmax : ℝ) (wmin_pos : 0 < wmin) (_wmin_le_wmax : wmin ≤ wmax)
    (Rmax σ F₁ F₂ : ℝ) : trussDesignGP hmin hmax wmin wmax Rmax σ F₁ F₂ := by
  -- Change variables.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence
      (fun (hwrA : ℝ × ℝ × ℝ × ℝ) =>
        (exp hwrA.1, exp hwrA.2.1, exp hwrA.2.2.1, exp hwrA.2.2.2))
    · rintro ⟨h, w, r, A⟩ ⟨c_r, _, _, c_hmin, _, c_wmin, _, c_A_lb, _⟩; dsimp at *
      split_ands
      · exact lt_of_lt_of_le hmin_pos c_hmin
      · exact lt_of_lt_of_le wmin_pos c_wmin
      · exact c_r
      · have h_A_div_2π_pos : 0 < A / (2 * π) := lt_of_lt_of_le (by positivity) c_A_lb
        rwa [div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)] at h_A_div_2π_pos
  conv_opt => dsimp
  rename_vars [h', w', r', A']
  remove_constr c_r => positivity

#print trussDesignConvex
-- optimization (h' : ℝ) (w' : ℝ) (r' : ℝ) (A' : ℝ)
--   minimize 2 * rexp A' * sqrt (rexp w' ^ 2 + rexp h' ^ 2)
--   subject to
--     c_F₁ : F₁ * sqrt (rexp w' ^ 2 + rexp h' ^ 2) / (2 * rexp h') ≤ σ * rexp A'
--     c_F₂ : F₂ * sqrt (rexp w' ^ 2 + rexp h' ^ 2) / (2 * rexp w') ≤ σ * rexp A'
--     c_hmin : hmin ≤ rexp h'
--     c_hmax : rexp h' ≤ hmax
--     c_wmin : wmin ≤ rexp w'
--     c_wmax : rexp w' ≤ wmax
--     c_A_lb : 0.21 * rexp r' ^ 2 ≤ rexp A' / (2 * π)
--     c_A_ub : sqrt (rexp A' / (2 * π) + rexp r' ^ 2) ≤ Rmax

end TrussDesign

end
