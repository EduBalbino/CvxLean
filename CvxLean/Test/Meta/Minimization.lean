import CvxLean.Meta.Minimization
import CvxLean.Syntax.Minimization
import CvxLean.Lib.Minimization
import Mathlib.Data.Real.Basic

/-!
# Tests for Meta/Minimization.lean

Golden output tests for the core Minimization expression infrastructure.

## Findings

**FINDING 1:** `ToExpr (Minimization D R)` does not exist. Tests must work with
expressions obtained through elaboration, not via `toExpr` on Minimization values.

## Test Coverage

- `decomposeDomain` / `composeDomain` - domain manipulation
- `decomposeConstraints` / `composeAnd` - constraint manipulation
- `mkProjections` - variable projection creation
- `getVariableNameSet` / `getConstraintNameSet` - name extraction
- `generateNewName` - fresh name generation
- `MinimizationExpr.fromExpr` / `toExpr` - expression parsing (via elab)

## Expected Behavior

These tests document the expected output of Meta operations. Failures indicate
behavioral changes that need investigation.
-/

namespace CvxLean.Test.Meta.Minimization

open Lean Lean.Meta CvxLean CvxLean.Meta

/-! ## Pure Expression Tests (no Minimization values needed) -/

section PureExprTests

/-- Test: `composeAnd` creates And-connected expression. -/
def testComposeAnd : MetaM Unit := do
  let c1 := mkConst ``True
  let c2 := mkConst ``True
  let c3 := mkConst ``True
  let composed := composeAnd [c1, c2, c3]
  -- Should be: And True (And True True)
  guard (composed.isAppOf ``And) <|> throwError "Expected And at top level"

/-- Test: Empty constraint list produces True. -/
def testComposeAndEmpty : MetaM Unit := do
  let composed := composeAnd []
  guard (composed.isConstOf ``True) <|> throwError "Expected True for empty list"

/-- Test: Single constraint returns itself. -/
def testComposeAndSingle : MetaM Unit := do
  let c := mkConst ``True
  let composed := composeAnd [c]
  guard (← isDefEq c composed) <|> throwError "Single constraint should return itself"

/-- Test: `decomposeAnd` extracts And components. -/
def testDecomposeAnd : MetaM Unit := do
  let c1 := mkConst ``True
  let c2 := mkConst ``True
  let composed := mkApp2 (mkConst ``And) c1 c2
  let decomposed ← decomposeAnd composed
  guard (decomposed.length == 2) <|> throwError "Expected 2 components"

/-- Test: `decomposeAnd` on single proposition returns singleton. -/
def testDecomposeAndSingle : MetaM Unit := do
  let c := mkConst ``True
  let decomposed ← decomposeAnd c
  guard (decomposed.length == 1) <|> throwError "Expected 1 component"

#eval testComposeAnd
#eval testComposeAndEmpty
#eval testComposeAndSingle
#eval testDecomposeAnd
#eval testDecomposeAndSingle

end PureExprTests

/-! ## Domain Composition Tests -/

section DomainTests

/-- Test: `composeDomain` creates labeled product for multiple vars. -/
def testComposeDomainMultiple : MetaM Unit := do
  let vars : List (Name × Expr) := [(`x, mkConst ``Real), (`y, mkConst ``Real)]
  let domain := composeDomain vars
  guard (domain.isAppOf ``Prod) <|> throwError "Expected Prod for multiple variables"

/-- Test: `composeDomain` creates labeled type for single var. -/
def testComposeDomainSingle : MetaM Unit := do
  let vars : List (Name × Expr) := [(`x, mkConst ``Real)]
  let domain := composeDomain vars
  -- Single variable should be labeled, not a Prod
  guard (!domain.isAppOf ``Prod) <|> throwError "Single var should not be Prod"

/-- Test: `composeDomain` creates Unit for empty list. -/
def testComposeDomainEmpty : MetaM Unit := do
  let vars : List (Name × Expr) := []
  let domain := composeDomain vars
  guard (domain.isConstOf ``Unit) <|> throwError "Empty list should give Unit"

/-- Test: `decomposeDomain` → `composeDomain` round-trip on constructed domain. -/
def testDomainRoundTrip : MetaM Unit := do
  let vars : List (Name × Expr) := [(`x, mkConst ``Real), (`y, mkConst ``Real)]
  let domain := composeDomain vars
  let decomposed ← decomposeDomain domain
  guard (decomposed.length == 2) <|> throwError "Expected 2 variables after decompose"
  let recomposed := composeDomain decomposed
  guard (← isDefEq domain recomposed) <|> throwError "Round-trip failed"

#eval testComposeDomainMultiple
#eval testComposeDomainSingle
#eval testComposeDomainEmpty
#eval testDomainRoundTrip

end DomainTests

/-! ## Name Generation Tests -/

section NameTests

/-- Test: `generateNewName` avoids existing names. -/
def testGenerateNewName : MetaM Unit := do
  let existing : Std.HashSet Name := ({} : Std.HashSet Name).insert `x1 |>.insert `x2
  let newName ← generateNewName "x" existing
  guard (newName == `x3) <|> throwError "Expected `x3`, got {newName}"

/-- Test: `generateNewName` starts from 1 for empty set. -/
def testGenerateNewNameEmpty : MetaM Unit := do
  let existing : Std.HashSet Name := {}
  let newName ← generateNewName "y" existing
  guard (newName == `y1) <|> throwError "Expected `y1`, got {newName}"

/-- Test: `generateNewName` handles gaps in numbering. -/
def testGenerateNewNameGap : MetaM Unit := do
  -- Has x1 and x3, should generate x2
  let existing : Std.HashSet Name := ({} : Std.HashSet Name).insert `x1 |>.insert `x3
  let newName ← generateNewName "x" existing
  -- Actually generates x2 since it tries sequentially from 1
  guard (newName == `x2) <|> throwError "Expected `x2`, got {newName}"

/-- Test: `getVariableNameSet` on composed domain. -/
def testGetVariableNameSet : MetaM Unit := do
  let vars : List (Name × Expr) := [(`x, mkConst ``Real), (`y, mkConst ``Real), (`z, mkConst ``Real)]
  let domain := composeDomain vars
  let nameSet ← getVariableNameSet domain
  guard (nameSet.contains `x) <|> throwError "Expected `x` in name set"
  guard (nameSet.contains `y) <|> throwError "Expected `y` in name set"
  guard (nameSet.contains `z) <|> throwError "Expected `z` in name set"
  guard (nameSet.size == 3) <|> throwError "Expected 3 names in set"

#eval testGenerateNewName
#eval testGenerateNewNameEmpty
#eval testGenerateNewNameGap
#eval testGetVariableNameSet

end NameTests

/-! ## Projection Tests -/

section ProjectionTests

/-- Test: `mkProjections` creates projections for two-variable domain. -/
def testMkProjections2 : MetaM Unit := do
  let vars : List (Name × Expr) := [(`x, mkConst ``Real), (`y, mkConst ``Real)]
  let domain := composeDomain vars
  withLocalDecl `p .default domain fun p => do
    let projs ← mkProjections domain p
    guard (projs.length == 2) <|> throwError "Expected 2 projections"
    let (name1, _, def1) := projs[0]!
    let (name2, _, def2) := projs[1]!
    guard (name1 == `x) <|> throwError "Expected first projection name `x`"
    guard (name2 == `y) <|> throwError "Expected second projection name `y`"
    guard (def1.isAppOf ``Prod.fst) <|> throwError "Expected Prod.fst for first projection"
    guard (def2.isAppOf ``Prod.snd) <|> throwError "Expected Prod.snd for second projection"

/-- Test: `mkProjections` creates nested projections for three variables. -/
def testMkProjections3 : MetaM Unit := do
  let vars : List (Name × Expr) := [(`x, mkConst ``Real), (`y, mkConst ``Real), (`z, mkConst ``Real)]
  let domain := composeDomain vars
  withLocalDecl `p .default domain fun p => do
    let projs ← mkProjections domain p
    guard (projs.length == 3) <|> throwError "Expected 3 projections"
    let (name1, _, _) := projs[0]!
    let (name2, _, _) := projs[1]!
    let (name3, _, _) := projs[2]!
    guard (name1 == `x) <|> throwError "Expected first projection name `x`"
    guard (name2 == `y) <|> throwError "Expected second projection name `y`"
    guard (name3 == `z) <|> throwError "Expected third projection name `z`"

/-- Test: `mkProjections` for single variable returns identity-like projection. -/
def testMkProjections1 : MetaM Unit := do
  let vars : List (Name × Expr) := [(`x, mkConst ``Real)]
  let domain := composeDomain vars
  withLocalDecl `p .default domain fun p => do
    let projs ← mkProjections domain p
    guard (projs.length == 1) <|> throwError "Expected 1 projection"
    let (name1, _, def1) := projs[0]!
    guard (name1 == `x) <|> throwError "Expected projection name `x`"
    -- For single var, the projection should be p itself (no Prod.fst needed)
    guard (← isDefEq def1 p) <|> throwError "Single var projection should be identity"

#eval testMkProjections2
#eval testMkProjections3
#eval testMkProjections1

end ProjectionTests

/-! ## MinimizationExpr Tests (via elaboration) -/

section MinimizationExprTests

/-- Test: `MinimizationExpr.fromExpr` parses manually constructed Minimization.mk. -/
def testFromExprManual : MetaM Unit := do
  -- Construct: Minimization.mk ℝ ℝ (fun x => x) (fun x => True)
  let domain := mkConst ``Real
  let codomain := mkConst ``Real
  let objFun := mkLambda `x .default domain (mkBVar 0)
  let constraints := mkLambda `x .default domain (mkConst ``True)
  let minExpr := mkApp4 (mkConst ``Minimization.mk) domain codomain objFun constraints
  let parsed ← MinimizationExpr.fromExpr minExpr
  guard (← isDefEq parsed.domain domain) <|> throwError "Domain mismatch"
  guard (← isDefEq parsed.codomain codomain) <|> throwError "Codomain mismatch"

/-- Test: `MinimizationExpr.toExpr` reconstructs expression. -/
def testToExprRoundTrip : MetaM Unit := do
  let domain := mkConst ``Real
  let codomain := mkConst ``Real
  let objFun := mkLambda `x .default domain (mkBVar 0)
  let constraints := mkLambda `x .default domain (mkConst ``True)
  let original := mkApp4 (mkConst ``Minimization.mk) domain codomain objFun constraints
  let parsed ← MinimizationExpr.fromExpr original
  let reconstructed := parsed.toExpr
  guard (← isDefEq original reconstructed) <|> throwError "Round-trip failed"

/-- Test: `MinimizationExpr.fromExpr` fails on non-Minimization expression. -/
def testFromExprError : MetaM Bool := do
  try
    let _ ← MinimizationExpr.fromExpr (mkConst ``Nat)
    return false  -- Should have thrown
  catch _ =>
    return true   -- Expected error

#eval testFromExprManual
#eval testToExprRoundTrip
#eval do guard (← testFromExprError) <|> throwError "Expected error for non-Minimization expr"

end MinimizationExprTests

/-! ## Integration Tests with Real Problems -/

noncomputable section IntegrationTests

/-- Single variable problem for integration testing. -/
def p1 := optimization (x : ℝ)
  minimize x

/-- Two variable problem. -/
def p2 := optimization (x y : ℝ)
  minimize x + y

/-- Problem with constraints. -/
def p3 := optimization (x : ℝ)
  minimize x
  subject to
    h₁ : 0 ≤ x

-- These verify the problems compile and have correct types
#check (p1 : Minimization ℝ ℝ)
#check (p2 : Minimization (ℝ × ℝ) ℝ)
#check (p3 : Minimization ℝ ℝ)

-- Verify structure access works
example : p1.objFun = fun x => x := rfl
example : p2.objFun = fun p => p.1 + p.2 := rfl
example : p3.constraints = fun x => 0 ≤ x := rfl

end IntegrationTests

end CvxLean.Test.Meta.Minimization
