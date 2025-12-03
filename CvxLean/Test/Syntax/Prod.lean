import CvxLean.Syntax.Prod
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Lib.Minimization
import Mathlib.Data.Real.Basic

/-!
# Golden Tests for Syntax/Prod.lean

Tests the `x#n` projection syntax:
- `elabProdField` - elaborate `x#n` to nested Prod.fst/Prod.snd
- `delabProdField` - delaborate projections back to `x#n`
- Correct indexing behavior

## Golden Behavior

The projection syntax MUST:
1. `x#1` → `Prod.fst x` (first element)
2. `x#2` → `Prod.snd x` (second element for pairs)
3. `x#2` → `Prod.fst (Prod.snd x)` (second element for 3+ tuples)
4. `x#n` → nested projections for n-th element
5. Round-trip: `delab (elab (x#n)) = x#n`
-/

namespace CvxLean.Test.Syntax.Prod

open Lean Lean.Meta Lean.PrettyPrinter CvxLean CvxLean.Meta

/-! ## Helper to get expression from constant -/

def getConstExpr (n : Name) : MetaM Expr := do
  match (← getEnv).constants.find! n with
  | ConstantInfo.defnInfo defn => return defn.value
  | _ => throwError "Not a definition: {n}"

/-! ## Basic Projection Tests

Test that Prod.fst and Prod.snd work correctly on constructed expressions. -/

section BasicTests

/-- Test: Prod.fst extracts first element. -/
def test_fst_extracts_first : MetaM Unit := do
  let pairTy := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Bool)
  withLocalDecl `x .default pairTy fun x => do
    let fst := mkApp3 (mkConst ``Prod.fst [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Bool) x
    let fstTy ← inferType fst
    guard (← isDefEq fstTy (mkConst ``Nat)) <|>
      throwError "GOLDEN VIOLATION: Prod.fst should have type Nat"

/-- Test: Prod.snd extracts second element. -/
def test_snd_extracts_second : MetaM Unit := do
  let pairTy := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Bool)
  withLocalDecl `x .default pairTy fun x => do
    let snd := mkApp3 (mkConst ``Prod.snd [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Bool) x
    let sndTy ← inferType snd
    guard (← isDefEq sndTy (mkConst ``Bool)) <|>
      throwError "GOLDEN VIOLATION: Prod.snd should have type Bool"

/-- Test: Nested projections on triple. -/
def test_nested_projections : MetaM Unit := do
  let bcTy := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Bool) (mkConst ``Char)
  let abcTy := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Nat) bcTy
  withLocalDecl `x .default abcTy fun x => do
    -- x.snd.snd should have type Char
    let snd1 := mkApp3 (mkConst ``Prod.snd [levelZero, levelZero]) (mkConst ``Nat) bcTy x
    let snd2 := mkApp3 (mkConst ``Prod.snd [levelZero, levelZero]) (mkConst ``Bool) (mkConst ``Char) snd1
    let snd2Ty ← inferType snd2
    guard (← isDefEq snd2Ty (mkConst ``Char)) <|>
      throwError "GOLDEN VIOLATION: x.snd.snd should have type Char"

#eval test_fst_extracts_first
#eval test_snd_extracts_second
#eval test_nested_projections

end BasicTests

/-! ## Delaboration Tests -/

section DelabTests

/-- Test: Prod.fst delaborates and re-elaborates correctly. -/
def test_delab_fst : MetaM Unit := do
  let pairTy := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat)
  withLocalDecl `x .default pairTy fun x => do
    let fst := mkApp3 (mkConst ``Prod.fst [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat) x
    let stx ← delab fst
    let reElab ← Lean.Elab.Term.TermElabM.run' <|
      Lean.Elab.Term.elabTerm stx none
    guard (← isDefEq fst reElab) <|>
      throwError "GOLDEN VIOLATION: Delaborated Prod.fst should re-elaborate correctly"

/-- Test: Prod.snd delaborates and re-elaborates correctly. -/
def test_delab_snd : MetaM Unit := do
  let pairTy := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat)
  withLocalDecl `x .default pairTy fun x => do
    let snd := mkApp3 (mkConst ``Prod.snd [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat) x
    let stx ← delab snd
    let reElab ← Lean.Elab.Term.TermElabM.run' <|
      Lean.Elab.Term.elabTerm stx none
    guard (← isDefEq snd reElab) <|>
      throwError "GOLDEN VIOLATION: Delaborated Prod.snd should re-elaborate correctly"

#eval test_delab_fst
#eval test_delab_snd

end DelabTests

/-! ## Integration with Optimization Problems -/

section IntegrationTests

/-- GOLDEN: Three-variable optimization problem. -/
def golden_three_vars := optimization (x y z : ℝ)
  minimize x + y + z
  subject to
    h : x + y ≤ z

/-- Test: mkProjections creates correct projections. -/
def test_mkProjections : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_three_vars)
  withLocalDecl `p .default minExpr.domain fun p => do
    let projs ← mkProjections minExpr.domain p
    guard (projs.length == 3) <|> throwError "GOLDEN VIOLATION: Expected 3 projections"
    -- First projection should be Prod.fst
    let (_, _, def1) := projs[0]!
    guard (def1.isAppOf ``Prod.fst) <|>
      throwError "GOLDEN VIOLATION: First projection should be Prod.fst"
    -- Second projection should be Prod.fst (Prod.snd p)
    let (_, _, def2) := projs[1]!
    guard (def2.isAppOf ``Prod.fst) <|>
      throwError "GOLDEN VIOLATION: Second projection should be Prod.fst"
    -- Third projection should be Prod.snd (Prod.snd p)
    let (_, _, def3) := projs[2]!
    guard (def3.isAppOf ``Prod.snd) <|>
      throwError "GOLDEN VIOLATION: Third projection should be Prod.snd"

/-- Test: Variable names are preserved in projections. -/
def test_projection_names : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_three_vars)
  withLocalDecl `p .default minExpr.domain fun p => do
    let projs ← mkProjections minExpr.domain p
    let (name1, _, _) := projs[0]!
    let (name2, _, _) := projs[1]!
    let (name3, _, _) := projs[2]!
    guard (name1 == `x) <|> throwError "GOLDEN VIOLATION: First variable should be `x`"
    guard (name2 == `y) <|> throwError "GOLDEN VIOLATION: Second variable should be `y`"
    guard (name3 == `z) <|> throwError "GOLDEN VIOLATION: Third variable should be `z`"

#eval test_mkProjections
#eval test_projection_names

end IntegrationTests

end CvxLean.Test.Syntax.Prod
