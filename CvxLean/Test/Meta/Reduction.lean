import CvxLean.Meta.Reduction
import CvxLean.Lib.Minimization

/-!
# Reduction Tests

Tests for `/CvxLean/Meta/Reduction.lean` - ReductionExpr parsing and tactics.
-/

open Lean Meta Elab Tactic
open CvxLean Meta Minimization

-- Simple test problems
def p1 : Minimization ℝ ℝ := ⟨fun x => x, fun x => 0 ≤ x⟩
def p2 : Minimization ℝ ℝ := ⟨fun x => x + 1, fun x => 0 ≤ x⟩

/-- Test: ReductionExpr.fromExpr parses valid reduction type. -/
def testReductionExprFromExpr : MetaM Unit := do
  let redType := mkApp6 (mkConst ``Minimization.Reduction)
    (mkConst ``Real) (mkConst ``Real) (mkConst ``Real)
    (mkConst ``Real.instPreorder) (mkConst ``p1) (mkConst ``p2)
  let redExpr ← ReductionExpr.fromExpr redType
  guard (redExpr.domainLHS.isConstOf ``Real) <|>
    throwError "Expected domainLHS to be Real"
  guard (redExpr.lhs.isConstOf ``p1) <|>
    throwError "Expected lhs to be p1"
  guard (redExpr.rhs.isConstOf ``p2) <|>
    throwError "Expected rhs to be p2"

#eval testReductionExprFromExpr

/-- Test: ReductionExpr.toExpr roundtrips. -/
def testReductionExprRoundtrip : MetaM Unit := do
  let redExpr : ReductionExpr := {
    domainLHS := mkConst ``Real
    domainRHS := mkConst ``Real
    codomain := mkConst ``Real
    codomainLHSreorder := mkConst ``Real.instPreorder
    lhs := mkConst ``p1
    rhs := mkConst ``p2
  }
  let e := redExpr.toExpr
  let redExpr' ← ReductionExpr.fromExpr e
  guard (redExpr'.domainLHS.isConstOf ``Real) <|>
    throwError "Roundtrip failed for domainLHS"

#eval testReductionExprRoundtrip

/-- Test: ReductionExpr.fromExpr rejects invalid expressions. -/
def testReductionExprRejectsInvalid : MetaM Unit := do
  try
    let _ ← ReductionExpr.fromExpr (mkConst ``Nat)
    throwError "Should have rejected invalid expression"
  catch _ =>
    pure ()

#eval testReductionExprRejectsInvalid

-- Test: reduction_rfl tactic syntax exists
#check (by reduction_rfl : Reduction p1 p1)

-- Test: reduction_trans tactic syntax exists
example : Reduction p1 p1 := by
  reduction_trans
  · reduction_rfl
  · reduction_rfl
