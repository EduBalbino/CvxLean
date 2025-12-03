import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Lib.Math.Data.Vec

/-!
Norm atoms (convex).

### L2 Norm

In Mathlib 4.26+, `‖x‖` on `Fin n → ℝ` is the sup norm, not the L2 norm.
We use `Vec.l2Norm` for the L2 norm, which is defined as `‖WithLp.toLp 2 x‖`.

### TODO

This is not defined in full generality. It can be made increasing or decreasing in each `xᵢ`
depending on the sign of `xᵢ`. Only affine arguments are accepted for now.
-/

namespace CvxLean

open Real

declare_atom l2norm [convex] (n : Nat)& (x : Fin n → ℝ)? : Vec.l2Norm x :=
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c : soCone t x)
solution (t := Vec.l2Norm x)
solutionEqualsAtom by rfl
feasibility
  (c : by
    unfold soCone Vec.l2Norm
    rw [EuclideanSpace.norm_eq]
    simp only [norm_eq_abs, sq_abs, rpow_two]
    exact le_refl _)
optimality by
  rw [soCone_iff_l2Norm_le] at c
  exact c
vconditionElimination

declare_atom norm2₂ [convex] (x : ℝ)? (y : ℝ)? : sqrt (x ^ 2 + y ^ 2) :=
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c : soCone t ![x, y])
solution (t := sqrt (x ^ 2 + y ^ 2))
solutionEqualsAtom by rfl
feasibility
  (c : by simp [soCone])
optimality by
  simp [soCone] at c
  simp [c]
vconditionElimination

declare_atom Vec.norm [convex] (n : Nat)& (m : Nat)&  (x : Fin n → Fin m → ℝ)? : Vec.norm x :=
vconditions
implementationVars (t : Fin n → ℝ)
implementationObjective (t)
implementationConstraints
  (c : Vec.soCone t x)
solution (t := Vec.norm x)
solutionEqualsAtom by rfl
feasibility
  (c : by
    unfold Vec.soCone soCone Vec.norm Vec.l2Norm
    simp only [EuclideanSpace.norm_eq, rpow_two, norm_eq_abs, sq_abs]
    intro; rfl)
optimality by
  intro j
  have hj := c j
  rw [soCone_iff_l2Norm_le] at hj
  unfold Vec.norm
  exact hj
vconditionElimination

end CvxLean
