import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Defs

/-!
The Gram-Schmidt algorithm respects basis vectors.
-/

section GramSchmidt

open Finset Submodule Module InnerProductSpace

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {𝕜}

lemma repr_gramSchmidt_diagonal {i : ι} (b : Basis ι 𝕜 E) :
    b.repr (gramSchmidt 𝕜 b i) i = 1 := by
  rw [gramSchmidt_def, map_sub, Finsupp.sub_apply, Basis.repr_self, Finsupp.single_eq_same,
    sub_eq_self, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_zero]
  intros j hj
  rw [Finset.mem_Iio] at hj
  simp only [starProjection_singleton, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [gramSchmidt_triangular hj, mul_zero]

end GramSchmidt
