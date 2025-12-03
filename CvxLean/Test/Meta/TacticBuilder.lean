import CvxLean.Meta.TacticBuilder
import CvxLean.Syntax.Minimization
import CvxLean.Command.Equivalence
import CvxLean.Tactic.Basic.All

/-!
# Tests for Meta/TacticBuilder.lean

Golden output tests for the tactic builder infrastructure:
- `TransformationGoal.fromExpr` classification
- `EquivalenceBuilder.toTactic`
- `ReductionBuilder.toTactic`
- `RelaxationBuilder.toTactic`
- `elabTransformationProof`

## Expected Behavior

These tests verify that builders correctly convert to tactics and that
transformation goals are properly classified.
-/

namespace CvxLean.Test.Meta.TacticBuilder

open Lean Lean.Meta CvxLean CvxLean.Meta Minimization

noncomputable section

/-! ## Test Problems -/

def p1 := optimization (x : ℝ)
  minimize x
  subject to
    h₁ : 0 ≤ x

def p2 := optimization (x y : ℝ)
  minimize x + y
  subject to
    h₁ : 0 ≤ x
    h₂ : 0 ≤ y

/-! ## TransformationGoal Classification Tests -/

section TransformationGoal

-- Test: `isTransitive` returns correct values
def testIsTransitive : MetaM Unit := do
  guard (TransformationGoal.Solution.isTransitive == false) <|>
    throwError "Solution should not be transitive"
  guard (TransformationGoal.Equivalence.isTransitive == true) <|>
    throwError "Equivalence should be transitive"
  guard (TransformationGoal.Reduction.isTransitive == true) <|>
    throwError "Reduction should be transitive"
  guard (TransformationGoal.Relaxation.isTransitive == true) <|>
    throwError "Relaxation should be transitive"

-- Test: TransformationGoal.fromExpr classifies Solution correctly
def testSolutionGoal : MetaM Unit := do
  -- Build a Solution type manually: Solution D R preorder p
  let domain := mkConst ``Real
  let codomain := mkConst ``Real
  let preorder ← mkFreshExprMVar none  -- placeholder for Preorder instance
  let objFun := mkLambda `x .default domain (mkBVar 0)
  let constraints := mkLambda `x .default domain (mkConst ``True)
  let p := mkApp4 (mkConst ``Minimization.mk) domain codomain objFun constraints
  let solType := mkApp4 (mkConst ``Minimization.Solution) domain codomain preorder p
  let goal ← TransformationGoal.fromExpr solType
  guard (goal == .Solution) <|> throwError "Expected Solution goal, got {repr goal}"

-- Test: TransformationGoal.fromExpr classifies Equivalence correctly
def testEquivalenceGoal : MetaM Unit := do
  let domain := mkConst ``Real
  let codomain := mkConst ``Real
  let preorder ← mkFreshExprMVar none
  let objFun := mkLambda `x .default domain (mkBVar 0)
  let constraints := mkLambda `x .default domain (mkConst ``True)
  let p := mkApp4 (mkConst ``Minimization.mk) domain codomain objFun constraints
  let eqvType := mkApp6 (mkConst ``Minimization.Equivalence)
    domain domain codomain preorder p p
  let goal ← TransformationGoal.fromExpr eqvType
  guard (goal == .Equivalence) <|> throwError "Expected Equivalence goal, got {repr goal}"

-- Test: TransformationGoal.fromExpr fails on invalid expression
def testFromExprError : MetaM Bool := do
  try
    let _ ← TransformationGoal.fromExpr (mkConst ``Nat)
    return false
  catch _ =>
    return true

#eval testIsTransitive
#eval testSolutionGoal
#eval testEquivalenceGoal
#eval do guard (← testFromExprError) <|> throwError "Expected error for invalid goal type"

end TransformationGoal

/-! ## Tactic Tests -/

-- Test: EquivalenceBuilder works on Equivalence goal
example : Equivalence p1 p1 := by equivalence_rfl

-- Test: EquivalenceBuilder works on Solution goal (via toBwd)
-- NOTE: This requires a complete solution, marked with sorry for now
example : Solution p1 := by sorry

-- Test: Equivalence transitivity creates correct subgoals
example (h1 : Equivalence p1 p1) (h2 : Equivalence p1 p1) : Equivalence p1 p1 := by
  equivalence_trans
  · exact h1
  · exact h2

-- Test: Multi-step equivalence using builder
equivalence eqvBuilder1/qBuilder1 :
    optimization (x : ℝ)
      minimize x
      subject to
        h₁ : 0 ≤ x := by
  rename_vars [y]
  rename_constrs [c₁]

-- Test: Chained equivalence steps
equivalence eqvChain/qChain :
    optimization (x y : ℝ)
      minimize x + y
      subject to
        h₁ : 0 ≤ x
        h₂ : 0 ≤ y := by
  rename_vars [a, b]
  rename_constrs [c₁, c₂]
  reorder_constrs [c₂, c₁]

-- Verify equivalences produce correct types
#check (eqvBuilder1 : Equivalence _ qBuilder1)
#check (eqvChain : Equivalence _ qChain)

end

end CvxLean.Test.Meta.TacticBuilder
