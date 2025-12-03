import CvxLean
import CvxLean.Command.Util.TimeCmd

/-!
# Case study: Aerospace Design via Quasiconvex Optimization

See https://www.cvxpy.org/examples/dqcp/hypersonic_shape_design.html.
-/

noncomputable section

namespace HypersonicShapeDesign

open CvxLean Minimization Real

-- Height of rectangle.
variable (a : ℝ)

-- Width of rectangle.
variable (b : ℝ)

def hypersonicShapeDesign :=
  optimization (Δx : ℝ)
    minimize sqrt ((1 / Δx ^ 2) - 1)
    subject to
      h₁ : 10e-6 ≤ Δx
      h₂ : Δx ≤ 1
      h₃ : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ 2) ≤ 0

end HypersonicShapeDesign

end
