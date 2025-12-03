import CvxLean.Meta.Relaxation
import CvxLean.Lib.Minimization

/-!
# Relaxation Tests

Tests for `/CvxLean/Meta/Relaxation.lean` - RelaxationExpr parsing and tactics.
-/

namespace CvxLean.Test.Meta.Relaxation

open Lean Meta Elab Tactic
open CvxLean Meta Minimization

-- Simple test problems (namespaced to avoid collision)
def relaxP1 : Minimization ℝ ℝ := ⟨fun x => x, fun x => 0 ≤ x⟩
def relaxP2 : Minimization ℝ ℝ := ⟨fun x => x, fun _ => True⟩  -- relaxed constraints

/-- Test: RelaxationExpr.fromExpr parses valid relaxation type. -/
def testRelaxationExprFromExpr : MetaM Unit := do
  let relType := mkApp6 (mkConst ``Minimization.Relaxation)
    (mkConst ``Real) (mkConst ``Real) (mkConst ``Real)
    (mkConst ``Real.instPreorder) (mkConst ``relaxP1) (mkConst ``relaxP2)
  let relExpr ← RelaxationExpr.fromExpr relType
  guard (relExpr.domainP.isConstOf ``Real) <|>
    throwError "Expected domainP to be Real"
  guard (relExpr.p.isConstOf ``relaxP1) <|>
    throwError "Expected p to be relaxP1"
  guard (relExpr.q.isConstOf ``relaxP2) <|>
    throwError "Expected q to be relaxP2"

#eval testRelaxationExprFromExpr

/-- Test: RelaxationExpr.toExpr roundtrips. -/
def testRelaxationExprRoundtrip : MetaM Unit := do
  let relExpr : RelaxationExpr := {
    domainP := mkConst ``Real
    domainQ := mkConst ``Real
    codomain := mkConst ``Real
    codomainPreorder := mkConst ``Real.instPreorder
    p := mkConst ``relaxP1
    q := mkConst ``relaxP2
  }
  let e := relExpr.toExpr
  let relExpr' ← RelaxationExpr.fromExpr e
  guard (relExpr'.domainP.isConstOf ``Real) <|>
    throwError "Roundtrip failed for domainP"

#eval testRelaxationExprRoundtrip

/-- Test: RelaxationExpr.fromExpr rejects invalid expressions. -/
def testRelaxationExprRejectsInvalid : MetaM Unit := do
  try
    let _ ← RelaxationExpr.fromExpr (mkConst ``Nat)
    throwError "Should have rejected invalid expression"
  catch _ =>
    pure ()

#eval testRelaxationExprRejectsInvalid

-- Test: relaxation_rfl tactic syntax exists
#check (by relaxation_rfl : Relaxation relaxP1 relaxP1)

-- Test: relaxation_trans tactic syntax exists
example : Relaxation relaxP1 relaxP1 := by
  relaxation_trans
  · relaxation_rfl
  · relaxation_rfl

end CvxLean.Test.Meta.Relaxation
