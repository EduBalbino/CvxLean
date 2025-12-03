import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import CvxLean.Lib.Math.Analysis.InnerProductSpace.GramSchmidtOrtho
import CvxLean.Lib.Math.LinearAlgebra.Matrix.Triangular

/-!
More results about LDL factorization (see `Mathlib.Analysis.Matrix.LDL`).
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [LinearOrder n] [WellFoundedLT n] [LocallyFiniteOrderBot n]

namespace LDL

open Matrix

open scoped Matrix ComplexOrder

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

@[simp]
lemma lowerInv_diagonal (i : n) : lowerInv hS i i = 1 := by
  letI := Sᵀ.toNormedAddCommGroup hS.transpose
  letI := Sᵀ.toInnerProductSpace hS.transpose.posSemidef
  simp only [lowerInv_eq_gramSchmidtBasis, transpose_apply, Module.Basis.toMatrix_apply,
      InnerProductSpace.coe_gramSchmidtBasis, repr_gramSchmidt_diagonal]

lemma lower_eq_to_matrix :
    lower hS =
      ((@InnerProductSpace.gramSchmidtBasis 𝕜 (n → 𝕜) _
        (Sᵀ.toNormedAddCommGroup hS.transpose)
        (Sᵀ.toInnerProductSpace hS.transpose.posSemidef)
        n _ _ _ (Pi.basisFun 𝕜 n)).toMatrix (Pi.basisFun 𝕜 n))ᵀ := by
  simp only [lower, lowerInv_eq_gramSchmidtBasis]
  apply Matrix.inv_eq_left_inv
  rw [← transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, transpose_one]

lemma lowerTriangular_lowerInv : lowerTriangular (lowerInv hS) := by
  apply lowerInv_triangular

lemma lowerTriangular_lower : lowerTriangular (lower hS) :=
  lowerTriangular_inv_of_lowerTriangular (lowerTriangular_lowerInv hS)

noncomputable instance invertible_lower : Invertible (lower hS) :=
  invertibleOfLeftInverse _ _ (mul_inv_of_invertible (lowerInv hS))

@[simp]
lemma inv_lower_eq_lowerInv : (lower hS)⁻¹ = lowerInv hS :=
  inv_eq_left_inv (mul_inv_of_invertible (lowerInv hS))

@[simp]
lemma lower_diagonal (i : n) : lower hS i i = 1 := by
  simpa using
    diag_inv_mul_diag_eq_one_of_lowerTriangular (lowerTriangular_lower hS) i

@[simp]
lemma det_lowerInv : (lowerInv hS).det = 1 := by
  have h := det_of_lowerTriangular (lowerInv hS) (by apply lowerInv_triangular)
  rw [h, Finset.prod_eq_one]
  intros
  rw [lowerInv_diagonal]

@[simp]
lemma det_lower : (lower hS).det = 1 := by
  simp [lower]

end LDL
