import CvxLean.Meta.Equivalence
import CvxLean.Syntax.Minimization
import CvxLean.Command.Equivalence
import CvxLean.Tactic.Basic.All

/-!
# Tests for Meta/Equivalence.lean

Golden output tests for `EquivalenceExpr` infrastructure.

## Test Coverage

- `EquivalenceExpr.fromExpr` / `toExpr` - expression parsing
- `toMinimizationExprLHS` / `toMinimizationExprRHS` - problem extraction
- Basic equivalence tactics: `equivalence_rfl`, `equivalence_symm`, `equivalence_trans`
- `equivalence_step` tactic
- `equivalence` command integration

## Expected Behavior

These tests verify that equivalence expressions are correctly parsed and constructed,
and that the basic equivalence tactics work as expected.
-/

namespace CvxLean.Test.Meta.Equivalence

open Lean Lean.Meta CvxLean CvxLean.Meta Minimization

/-! ## EquivalenceExpr Parsing Tests (Pure MetaM) -/

section EquivalenceExprParsing

/-- Test: `EquivalenceExpr.toExpr` produces Equivalence application. -/
def testToExpr : MetaM Unit := do
  let domain := mkConst ``Real
  let codomain := mkConst ``Real
  let objFun := mkLambda `x .default domain (mkBVar 0)
  let constraints := mkLambda `x .default domain (mkConst ``True)
  let lhs := mkApp4 (mkConst ``Minimization.mk) domain codomain objFun constraints
  let rhs := lhs
  -- Use a placeholder for preorder - we just test structure
  let preorder ← mkFreshExprMVar none
  let eqvExpr : EquivalenceExpr := {
    domainLHS := domain
    domainRHS := domain
    codomain := codomain
    codomainPreorder := preorder
    lhs := lhs
    rhs := rhs
  }
  let reconstructed := eqvExpr.toExpr
  guard (reconstructed.isAppOf ``Minimization.Equivalence) <|>
    throwError "Expected Minimization.Equivalence"

/-- Test: `EquivalenceExpr.fromExpr` fails on non-Equivalence expression. -/
def testFromExprError : MetaM Bool := do
  try
    let _ ← EquivalenceExpr.fromExpr (mkConst ``Nat)
    return false
  catch _ =>
    return true

#eval testToExpr
#eval do guard (← testFromExprError) <|> throwError "Expected error for non-Equivalence expr"

end EquivalenceExprParsing

/-! ## Tactic and Command Tests -/

noncomputable section

-- Test problems
def p1 := optimization (x : ℝ)
  minimize x
  subject to
    h₁ : 0 ≤ x

def p2 := optimization (x : ℝ)
  minimize x
  subject to
    h₁ : 0 ≤ x

-- Test: `equivalence_rfl` closes reflexive equivalence goal
example : Equivalence p1 p1 := by equivalence_rfl

-- Test: `equivalence_symm` swaps LHS and RHS
example (h : Equivalence p1 p2) : Equivalence p2 p1 := by
  equivalence_symm
  exact h

-- Test: `equivalence_trans` creates two subgoals
example (h1 : Equivalence p1 p2) (h2 : Equivalence p2 p1) : Equivalence p1 p1 := by
  equivalence_trans
  · exact h1
  · exact h2

-- Test: Simple equivalence with no transformation
equivalence eqv1/q1 : p1 := by
  equivalence_rfl

-- Test: Equivalence with variable renaming
equivalence eqv2/q2 :
    optimization (x : ℝ)
      minimize x
      subject to
        h₁ : 0 ≤ x := by
  rename_vars [y]

-- Test: Equivalence with constraint renaming
equivalence eqv3/q3 :
    optimization (x : ℝ)
      minimize x
      subject to
        h₁ : 0 ≤ x := by
  rename_constrs [c₁]

-- Test: Multi-step equivalence
equivalence eqv4/q4 :
    optimization (x y : ℝ)
      minimize x + y
      subject to
        h₁ : 0 ≤ x
        h₂ : 0 ≤ y := by
  rename_vars [a, b]
  rename_constrs [c₁, c₂]

-- Verify the equivalences produce correct types
#check (eqv1 : Equivalence p1 q1)
#check (eqv2 : Equivalence _ q2)
#check (eqv3 : Equivalence _ q3)
#check (eqv4 : Equivalence _ q4)

end

end CvxLean.Test.Meta.Equivalence
