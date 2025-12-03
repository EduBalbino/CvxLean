import CvxLean.Syntax.Label
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Lib.Minimization
import Mathlib.Data.Real.Basic

/-!
# Golden Tests for Syntax/Label.lean

Tests the `CvxLeanLabel` metadata infrastructure:
- `mkLabel` - attach label to expression
- `decomposeLabel` - extract label from expression
- `getLabelName` - get just the name
- `{** term ** name **}` syntax
- Label preservation through transformations

## Golden Behavior

Labels MUST:
1. Be preserved through `mkLabel` → `decomposeLabel` round-trip
2. Store names in `MData` with key `CvxLeanLabel`
3. Not affect the semantic meaning of expressions
4. Be extractable from nested metadata
-/

namespace CvxLean.Test.Syntax.Label

open Lean Lean.Meta CvxLean CvxLean.Meta

/-! ## Helper to get expression from constant -/

def getConstExpr (n : Name) : MetaM Expr := do
  match (← getEnv).constants.find! n with
  | ConstantInfo.defnInfo defn => return defn.value
  | _ => throwError "Not a definition: {n}"

/-! ## mkLabel / decomposeLabel Tests -/

section BasicTests

/-- Test: mkLabel creates MData expression. -/
def test_mkLabel_creates_mdata : MetaM Unit := do
  let e := mkConst ``Nat
  let labeled := mkLabel `myName e
  guard labeled.isMData <|>
    throwError "GOLDEN VIOLATION: mkLabel should create MData expression"

/-- Test: decomposeLabel extracts correct name. -/
def test_decomposeLabel_name : MetaM Unit := do
  let e := mkConst ``Nat
  let labeled := mkLabel `testLabel e
  let (name, _) ← decomposeLabel labeled
  guard (name == `testLabel) <|>
    throwError "GOLDEN VIOLATION: decomposeLabel should return `testLabel`, got {name}"

/-- Test: decomposeLabel extracts correct expression. -/
def test_decomposeLabel_expr : MetaM Unit := do
  let e := mkConst ``Nat
  let labeled := mkLabel `testLabel e
  let (_, extracted) ← decomposeLabel labeled
  guard (← isDefEq e extracted) <|>
    throwError "GOLDEN VIOLATION: decomposeLabel should return original expression"

/-- Test: Round-trip mkLabel → decomposeLabel. -/
def test_label_roundtrip : MetaM Unit := do
  let e := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
  let name := `roundTripTest
  let labeled := mkLabel name e
  let (extractedName, extractedExpr) ← decomposeLabel labeled
  guard (extractedName == name) <|>
    throwError "GOLDEN VIOLATION: Name not preserved in round-trip"
  guard (← isDefEq extractedExpr e) <|>
    throwError "GOLDEN VIOLATION: Expression not preserved in round-trip"

/-- Test: getLabelName returns just the name. -/
def test_getLabelName : MetaM Unit := do
  let e := mkConst ``Bool
  let labeled := mkLabel `justTheName e
  let name ← getLabelName labeled
  guard (name == `justTheName) <|>
    throwError "GOLDEN VIOLATION: getLabelName should return `justTheName`"

/-- Test: Unlabeled expression returns anonymous name. -/
def test_unlabeled_anonymous : MetaM Unit := do
  let e := mkConst ``Int
  let (name, _) ← decomposeLabel e
  guard (name == `_) <|>
    throwError "GOLDEN VIOLATION: Unlabeled expression should have name `_`"

#eval test_mkLabel_creates_mdata
#eval test_decomposeLabel_name
#eval test_decomposeLabel_expr
#eval test_label_roundtrip
#eval test_getLabelName
#eval test_unlabeled_anonymous

end BasicTests

/-! ## Nested Label Tests -/

section NestedTests

/-- Test: decomposeLabel handles nested MData. -/
def test_nested_mdata : MetaM Unit := do
  let e := mkConst ``String
  -- Create nested metadata (not CvxLeanLabel)
  let inner := mkMData (MData.empty.setNat `otherKey 42) e
  let labeled := mkLabel `outerLabel inner
  let (name, _) ← decomposeLabel labeled
  guard (name == `outerLabel) <|>
    throwError "GOLDEN VIOLATION: Should extract outer CvxLeanLabel"

/-- Test: Multiple labels - outermost wins. -/
def test_multiple_labels : MetaM Unit := do
  let e := mkConst ``Unit
  let inner := mkLabel `innerLabel e
  let outer := mkLabel `outerLabel inner
  let (name, _) ← decomposeLabel outer
  guard (name == `outerLabel) <|>
    throwError "GOLDEN VIOLATION: Outermost label should be extracted"

#eval test_nested_mdata
#eval test_multiple_labels

end NestedTests

/-! ## Label Syntax Tests -/

section SyntaxTests

/-- Test: mkLabel directly creates labeled expression. -/
def test_mkLabel_direct : MetaM Unit := do
  let e := mkNatLit 42
  let labeled := mkLabel `directLabel e
  let (name, _) ← decomposeLabel labeled
  guard (name == `directLabel) <|>
    throwError "GOLDEN VIOLATION: mkLabel should create label `directLabel`"

#eval test_mkLabel_direct

end SyntaxTests

/-! ## Integration with Optimization Problems -/

section IntegrationTests

/-- GOLDEN: Problem with labeled constraints. -/
def golden_labeled := optimization (x y : ℝ)
  minimize x + y
  subject to
    positiveX : 0 ≤ x
    positiveY : 0 ≤ y
    sumBound : x + y ≤ 10

/-- Test: Constraint labels are preserved in optimization problems. -/
def test_optimization_labels : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_labeled)
  let constrs ← decomposeConstraints minExpr.constraints.bindingBody!
  guard (constrs.length == 3) <|> throwError "GOLDEN VIOLATION: Expected 3 constraints"
  guard (constrs[0]!.1 == `positiveX) <|>
    throwError "GOLDEN VIOLATION: First constraint should be `positiveX`"
  guard (constrs[1]!.1 == `positiveY) <|>
    throwError "GOLDEN VIOLATION: Second constraint should be `positiveY`"
  guard (constrs[2]!.1 == `sumBound) <|>
    throwError "GOLDEN VIOLATION: Third constraint should be `sumBound`"

/-- Test: Variable labels are preserved in domain. -/
def test_domain_labels : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_labeled)
  let vars ← decomposeDomain minExpr.domain
  guard (vars[0]!.1 == `x) <|>
    throwError "GOLDEN VIOLATION: First variable should be `x`"
  guard (vars[1]!.1 == `y) <|>
    throwError "GOLDEN VIOLATION: Second variable should be `y`"

/-- Test: Labels don't affect definitional equality. -/
def test_labels_transparent : MetaM Unit := do
  let labeled := mkLabel `someName (mkConst ``True)
  let unlabeled := mkConst ``True
  guard (← isDefEq labeled unlabeled) <|>
    throwError "GOLDEN VIOLATION: Labels should be transparent to definitional equality"

#eval test_optimization_labels
#eval test_domain_labels
#eval test_labels_transparent

end IntegrationTests

/-! ## Edge Cases -/

section EdgeCases

/-- Test: Empty name (anonymous). -/
def test_anonymous_label : MetaM Unit := do
  let e := mkSort levelZero  -- Prop
  let labeled := mkLabel Name.anonymous e
  let (name, _) ← decomposeLabel labeled
  guard (name == Name.anonymous) <|>
    throwError "GOLDEN VIOLATION: Anonymous name should be preserved"

/-- Test: Hierarchical name. -/
def test_hierarchical_name : MetaM Unit := do
  let e := mkSort (mkLevelSucc levelZero)  -- Type
  let name := `Foo.Bar.Baz
  let labeled := mkLabel name e
  let (extracted, _) ← decomposeLabel labeled
  guard (extracted == name) <|>
    throwError "GOLDEN VIOLATION: Hierarchical name should be preserved"

/-- Test: Numeric suffix name. -/
def test_numeric_name : MetaM Unit := do
  let e := mkConst ``Char
  let name := Name.num `x 1  -- `x.1 as a Name
  let labeled := mkLabel name e
  let (extracted, _) ← decomposeLabel labeled
  guard (extracted == name) <|>
    throwError "GOLDEN VIOLATION: Numeric suffix name should be preserved"

#eval test_anonymous_label
#eval test_hierarchical_name
#eval test_numeric_name

end EdgeCases

end CvxLean.Test.Syntax.Label
