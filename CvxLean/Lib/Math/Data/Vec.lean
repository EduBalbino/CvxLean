import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Fin

/-!
Extra vector functions and results. Some are needed to define atoms. Importantly, computable
versions of vector operations are defined here, which are used by the real-to-float procedure.
-/

namespace Vec

open Real BigOperators


/-- The L2 (Euclidean) norm for `Fin n → ℝ`. Defined as the norm on `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

/-- Convert to EuclideanSpace to use Mathlib lemmas. -/
lemma l2Norm_def {n : ℕ} (x : Fin n → ℝ) :
    l2Norm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := rfl

/-- The L2 norm equals `√(∑ i, x i ^ 2)`. -/
lemma l2Norm_eq_sqrt_sum {n : ℕ} (x : Fin n → ℝ) : l2Norm x = √(∑ i, x i ^ 2) := by
  rw [l2Norm_def, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [norm_eq_abs, sq_abs]

/-- The squared L2 norm equals the sum of squares. -/
lemma l2Norm_sq {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  rw [l2Norm_eq_sqrt_sum, rpow_two]
  have hnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => rpow_two (x i) ▸ sq_nonneg _)
  rw [Real.sq_sqrt hnn]

/-- Version of `l2Norm_sq` using `sq` (Nat power) instead of rpow. -/
lemma l2Norm_sq' {n : ℕ} (x : Fin n → ℝ) : (l2Norm x) ^ (2 : ℕ) = ∑ i, (x i) ^ (2 : ℕ) := by
  have h := l2Norm_sq x
  simp only [rpow_two] at h
  exact h

/-- The squared L2 norm of a difference. -/
lemma l2Norm_sub_sq {n : ℕ} (x y : Fin n → ℝ) :
    l2Norm (x - y) ^ 2 = l2Norm x ^ 2 + l2Norm y ^ 2 - 2 * ∑ i, x i * y i := by
  simp only [l2Norm_sq, Pi.sub_apply]
  have h : ∀ i : Fin n, (x i - y i) ^ (2 : ℝ) = x i ^ (2 : ℝ) - 2 * x i * y i + y i ^ (2 : ℝ) := by
    intro i
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmul : ∑ i : Fin n, 2 * x i * y i = 2 * ∑ i, x i * y i := by
    rw [Finset.mul_sum]; congr 1; funext i; ring
  simp only [hmul]
  ring

/-- Version of `l2Norm_sub_sq` using `sq` (Nat power) instead of rpow. -/
lemma l2Norm_sub_sq' {n : ℕ} (x y : Fin n → ℝ) :
    (l2Norm (x - y)) ^ (2 : ℕ) = (l2Norm x) ^ (2 : ℕ) + (l2Norm y) ^ (2 : ℕ) - 2 * ∑ i, x i * y i := by
  have h := l2Norm_sub_sq x y
  simp only [rpow_two] at h
  exact h

/-- L2 norm is nonnegative. -/
lemma l2Norm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ l2Norm x := by
  unfold l2Norm
  exact norm_nonneg _

/-- `√(a) ^ 2 = a` for nonnegative `a`. -/
lemma sqrt_sq_rpow {a : ℝ} (ha : 0 ≤ a) : √a ^ (2 : ℝ) = a := by
  rw [rpow_two, Real.sq_sqrt ha]

/-- `√(a) ^ 2 = a` for nonnegative `a`, stated with Nat power. -/
lemma sqrt_sq_nat {a : ℝ} (ha : 0 ≤ a) : √a ^ (2 : ℕ) = a :=
  Real.sq_sqrt ha

/-- Convert `x ^ (2 : ℝ)` to `x ^ (2 : ℕ)` for any real `x`. -/
lemma rpow_two_eq_sq (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := rpow_two x

/-- Convert `l2Norm x ^ (2 : ℝ)` to `l2Norm x ^ (2 : ℕ)`. -/
@[simp]
lemma l2Norm_rpow_two {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ (2 : ℝ) = l2Norm x ^ (2 : ℕ) :=
  rpow_two (l2Norm x)

/-- The squared L2 norm of a difference, expanded with Nat powers and dot product. -/
lemma l2Norm_sub_sq_expanded {n : ℕ} (x y : Fin n → ℝ) :
    (l2Norm (x - y)) ^ (2 : ℕ) =
    (l2Norm x) ^ (2 : ℕ) + (l2Norm y) ^ (2 : ℕ) - 2 * (x ⬝ᵥ y) := by
  rw [l2Norm_sub_sq']
  simp only [dotProduct]

/-- Rewrite `l2Norm (x - y) ^ 2` in terms of individual norms and dot product. -/
lemma l2Norm_sub_sq_dotProduct {n : ℕ} (x y : Fin n → ℝ) :
    l2Norm (x - y) ^ 2 = l2Norm x ^ 2 + l2Norm y ^ 2 - 2 * (x ⬝ᵥ y) := by
  rw [l2Norm_sub_sq]
  simp only [dotProduct]

/-- `√(t + l2Norm c ^ 2) ^ 2 = t + l2Norm c ^ 2` with Nat power. -/
lemma sqrt_add_l2Norm_sq_nat {n : ℕ} (t : ℝ) (c : Fin n → ℝ) (h : 0 ≤ t + l2Norm c ^ (2 : ℕ)) :
    √(t + l2Norm c ^ (2 : ℕ)) ^ (2 : ℕ) = t + l2Norm c ^ (2 : ℕ) :=
  Real.sq_sqrt h

/-- `√(t + l2Norm c ^ 2) ^ 2 = t + l2Norm c ^ 2` with rpow. -/
lemma sqrt_add_l2Norm_sq_rpow {n : ℕ} (t : ℝ) (c : Fin n → ℝ) (h : 0 ≤ t + l2Norm c ^ (2 : ℕ)) :
    √(t + l2Norm c ^ (2 : ℕ)) ^ (2 : ℝ) = t + l2Norm c ^ (2 : ℕ) := by
  rw [rpow_two, Real.sq_sqrt h]

/-- Nonnegativity of `t + l2Norm c ^ 2`. -/
lemma add_l2Norm_sq_nonneg {n : ℕ} (t : ℝ) (c : Fin n → ℝ) (h : 0 ≤ t + l2Norm c ^ (2 : ℕ)) :
    0 ≤ t + l2Norm c ^ (2 : ℕ) := h

/-!
Named functions on vectors. Each of them corresponds to an atom.
-/

universe u v w

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] {α : Type w}

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Abs`. -/
def abs (x : m → ℝ) : m → ℝ :=
  fun i => |x i|

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.VecConst`. -/
def const (n : ℕ) (k : α) : Fin n → α  :=
  fun _ => k

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.VecToMatrix`. -/
def toMatrix {n : ℕ} (x : Fin n → α) : Matrix (Fin n) (Fin 1) α :=
  fun i => ![x i]

def map {β} (f : α → β) (v : m → α) : m → β :=
  fun i => f (v i)

section AddCommMonoid

variable [AddCommMonoid α] {m : Nat} {n : Nat} (x : Fin m → α) (y : Fin n → α)

open BigOperators

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Sum`. -/
def sum {m : Type} [Fintype m] (x : m → α) : α :=
  ∑ i, x i

open FinsetInterval

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.CumSum`. -/
def cumsum (t : Fin n → α) : Fin n → α :=
  fun i => if h : 0 < n then ∑ j ∈ [[(⟨0, h⟩ : Fin n), i]], t j else 0

end AddCommMonoid


noncomputable section Real

/-!
Named functions on real vectors, including those defined in
`CvxLean.Lib.Math.Data.Real`. Each of them corresponds to an atom.
-/

variable (x y : m → ℝ)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Exp`. -/
def exp : m → ℝ := fun i => Real.exp (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Log`. -/
def log : m → ℝ := fun i => Real.log (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Entr`. -/
def entr : m → ℝ := fun i => Real.entr (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Huber`. -/
def huber : m → ℝ := fun i => Real.huber (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.KLDiv`. -/
def klDiv : m → ℝ := fun i => Real.klDiv (x i) (y i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Norm2`. -/
def norm {n m : ℕ} (x : Fin n → Fin m → ℝ) : Fin n → ℝ :=
  fun i => l2Norm (x i)

/-- The squared norm of each row as a function. -/
lemma norm_sq' {n m : ℕ} (x : Fin n → Fin m → ℝ) :
    (fun i => (norm x i) ^ (2 : ℕ)) = fun i => ∑ j, (x i j) ^ (2 : ℕ) := by
  funext i
  exact l2Norm_sq' (x i)

/-- Simp lemma for norm squared at index. -/
@[simp]
lemma norm_sq_apply' {n m : ℕ} (x : Fin n → Fin m → ℝ) (i : Fin n) :
    (norm x i) ^ (2 : ℕ) = ∑ j, (x i j) ^ (2 : ℕ) :=
  l2Norm_sq' (x i)

/-- The squared norm of each row as a function. -/
lemma norm_sq {n m : ℕ} (x : Fin n → Fin m → ℝ) :
    norm x ^ 2 = fun i => ∑ j, (x i j) ^ (2 : ℝ) := by
  funext i
  simp only [norm, Pi.pow_apply]
  exact l2Norm_sq (x i)

/-- Simp lemma for norm squared at index. -/
@[simp]
lemma norm_sq_apply {n m : ℕ} (x : Fin n → Fin m → ℝ) (i : Fin n) :
    (norm x i) ^ 2 = ∑ j, (x i j) ^ (2 : ℝ) :=
  l2Norm_sq (x i)

end Real


section RealLemmas

variable {a b c : m → ℝ}

omit [Fintype m] in
lemma div_le_iff (hb : StrongLT 0 b) : a / b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h i; have hi := h i; simp at hi
    rw [_root_.div_le_iff₀ (hb i)] at hi; exact hi
  · intro h i; have hi := h i; simp at hi
    dsimp; rw [_root_.div_le_iff₀ (hb i)]; exact hi

omit [Fintype m] in
lemma le_div_iff (hc : StrongLT 0 c) : a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h i; have hi := h i; simp at hi
    rw [_root_.le_div_iff₀ (hc i)] at hi; exact hi
  · intro h i; have hi := h i; simp at hi
    dsimp; rw [_root_.le_div_iff₀ (hc i)]; exact hi

end RealLemmas


namespace Computable

/-!
Computable operations on vectors used in `RealToFloat`.
-/

variable {n : ℕ}

def toArray (x : Fin n → Float) : Array Float :=
  (Array.range n).map (fun i => if h : i < n then x ⟨i, h⟩ else 0)

def sum (x : Fin n → Float) : Float :=
  (toArray x).foldl Float.add 0

def cumsum (x : Fin n → Float) : Fin n → Float :=
  fun i => (((toArray x).toList.take (i.val + 1)).foldl Float.add 0)

def _root_.Real.Computable.norm {n : ℕ} (x : Fin n → Float) : Float :=
  Float.sqrt (sum (fun i => (Float.pow (x i) 2)))

def norm {n m : ℕ} (A : Fin n → Fin m → Float) : Fin n → Float :=
  fun i => Real.Computable.norm (A i)

def exp {m} (x : m → Float) : m → Float :=
  fun i => Float.exp (x i)

end Computable

end Vec
