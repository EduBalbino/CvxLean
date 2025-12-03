import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
Results about the eigenspaces of the sum of two endomorphisms.
-/

universe u v w

namespace Module

namespace End

variable {K R : Type v} {V M : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Field K] [AddCommGroup V] [Module K V]

lemma eigenspace_add {f g : End R M} {a b : R} :
    eigenspace f a ⊓ eigenspace g b ≤ eigenspace (f + g) (a + b) := by
  rintro x ⟨hf, hg⟩
  rw [SetLike.mem_coe, mem_eigenspace_iff] at hf hg
  rw [mem_eigenspace_iff, LinearMap.add_apply, hf, hg, ← add_smul]

lemma eigenspace_one : eigenspace (1 : End R M) 1 = ⊤ := by
  apply eq_top_iff.2
  intros x _
  rw [mem_eigenspace_iff]
  simp only [one_apply, one_smul]

lemma has_eigenvector_add {f g : End R M} {a b : R} {x : M} (hf : HasEigenvector f a x)
    (hg : HasEigenvector g b x) : HasEigenvector (f + g) (a + b) x :=
  ⟨eigenspace_add ⟨hf.1, hg.1⟩, hf.2⟩

lemma has_eigenvector_one {x : M} (hx : x ≠ 0) : HasEigenvector (1 : End R M) 1 x := by
  rw [hasEigenvector_iff, eigenspace_one]
  exact ⟨Submodule.mem_top, hx⟩

end End

end Module
