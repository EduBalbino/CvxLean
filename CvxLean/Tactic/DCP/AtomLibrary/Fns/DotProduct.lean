import CvxLean.Tactic.DCP.AtomCmd

/-!
Dot product atom (affine).
-/

namespace CvxLean

declare_atom Vec.dotProduct1 [affine] (m : Nat)& (x : Fin m → ℝ)& (y : Fin m → ℝ)? :
  dotProduct x y :=
bconditions
homogenity by
  rw [dotProduct_zero, smul_zero, add_zero, add_zero,
      dotProduct_smul]
additivity by
  rw [dotProduct_zero, add_zero, dotProduct_add]
optimality le_refl _

declare_atom Vec.dotProduct2 [affine] (m : Nat)& (x : Fin m → ℝ)? (y : Fin m → ℝ)& :
  dotProduct x y :=
bconditions
homogenity by
  rw [zero_dotProduct, smul_zero, add_zero, add_zero,
      smul_dotProduct]
additivity by
  rw [zero_dotProduct, add_zero, add_dotProduct]
optimality le_refl _

end CvxLean
