import CvxLean.Meta.Util.Expr

/-!
# Tests for Meta/Util/Expr.lean

Golden output tests for expression manipulation utilities:
- `mkAndIntro` / `foldAndIntro`
- `foldProdMk`
- `mkExistsFVars` / `mkExistsIntro`
- `mkLetFVarsWith`
- `isConstant` / `isRelativelyConstant`
- `removeMData`
- `mkAppBeta` / `mkAppNBeta`
- `convertLambdasToLets`
- `Expr.size`
- `mkProd` / `mkArray`

## Expected Behavior

These tests verify that expression construction and manipulation utilities
produce the expected output structures.
-/

namespace CvxLean.Test.Meta.Util.Expr

open Lean Lean.Meta Lean.Expr

/-! ## And Introduction Tests -/

section AndIntro

/-- Test: `mkAndIntro` creates right-associative And.intro from proof terms. -/
def testMkAndIntro : MetaM Unit := do
  -- mkAndIntro expects PROOF TERMS, not propositions
  let t := mkConst ``True.intro  -- proof of True
  let result ← mkAndIntro #[t, t, t]
  -- Should be: And.intro True.intro (And.intro True.intro True.intro)
  guard (result.isAppOf ``And.intro) <|> throwError "Expected And.intro at top level"

/-- Test: `foldAndIntro` handles empty array. -/
def testFoldAndIntroEmpty : MetaM Unit := do
  let result ← foldAndIntro #[]
  guard (result.isConstOf ``True.intro) <|> throwError "Expected True.intro for empty array"

/-- Test: `foldAndIntro` handles single element. -/
def testFoldAndIntroSingle : MetaM Unit := do
  withLocalDecl `h .default (mkConst ``True) fun h => do
    let result ← foldAndIntro #[h]
    guard (← isDefEq result h) <|> throwError "Single element should return itself"

#eval testMkAndIntro
#eval testFoldAndIntroEmpty
#eval testFoldAndIntroSingle

end AndIntro

/-! ## Product Construction Tests -/

section ProdMk

/-- Test: `foldProdMk` creates nested products. -/
def testFoldProdMk : MetaM Unit := do
  withLocalDecl `x .default (mkConst ``Nat) fun x =>
  withLocalDecl `y .default (mkConst ``Nat) fun y =>
  withLocalDecl `z .default (mkConst ``Nat) fun z => do
    let result ← foldProdMk #[x, y, z]
    -- Should be: Prod.mk x (Prod.mk y z)
    guard (result.isAppOf ``Prod.mk) <|> throwError "Expected Prod.mk at top level"

/-- Test: `foldProdMk` with two elements. -/
def testFoldProdMk2 : MetaM Unit := do
  withLocalDecl `x .default (mkConst ``Nat) fun x =>
  withLocalDecl `y .default (mkConst ``Nat) fun y => do
    let result ← foldProdMk #[x, y]
    guard (result.isAppOf ``Prod.mk) <|> throwError "Expected Prod.mk"

/-- Test: `mkProd` creates product type. -/
def testMkProd : MetaM Unit := do
  let nat := mkConst ``Nat
  let result ← mkProd #[nat, nat, nat]
  guard (result.isAppOf ``Prod.mk) <|> throwError "Expected Prod.mk"

#eval testFoldProdMk
#eval testFoldProdMk2
#eval testMkProd

end ProdMk

/-! ## Existential Tests -/

section Existentials

/-- Test: `mkExistsFVars` creates nested existentials. -/
def testMkExistsFVars : MetaM Unit := do
  withLocalDecl `x .default (mkConst ``Nat) fun x =>
  withLocalDecl `y .default (mkConst ``Nat) fun y => do
    let body := mkConst ``True
    let result ← mkExistsFVars #[x, y] body
    -- Should be: ∃ x, ∃ y, True
    guard (result.isAppOf ``Exists) <|> throwError "Expected Exists at top level"

/-- Test: `mkExistsIntro` creates existential proof. -/
def testMkExistsIntro : MetaM Unit := do
  withLocalDecl `x .default (mkConst ``Nat) fun x => do
    let proof := mkConst ``True.intro
    let result ← mkExistsIntro #[x] proof
    guard (result.isAppOf ``Exists.intro) <|> throwError "Expected Exists.intro"

#eval testMkExistsFVars
#eval testMkExistsIntro

end Existentials

/-! ## Constant Detection Tests -/

section ConstantDetection

/-- Test: `isConstant` returns true for constants. -/
def testIsConstantTrue : MetaM Unit := do
  let e := mkConst ``Nat
  guard (isConstant e) <|> throwError "Constant should be detected as constant"

/-- Test: `isConstant` returns false for free variables. -/
def testIsConstantFalse : MetaM Unit := do
  withLocalDecl `x .default (mkConst ``Nat) fun x => do
    guard (!isConstant x) <|> throwError "FVar should not be constant"

/-- Test: `isRelativelyConstant` checks specific variables. -/
def testIsRelativelyConstant : MetaM Unit := do
  withLocalDecl `x .default (mkConst ``Nat) fun x =>
  withLocalDecl `y .default (mkConst ``Nat) fun y => do
    -- x is relatively constant w.r.t. [y]
    guard (isRelativelyConstant x #[y.fvarId!]) <|>
      throwError "x should be relatively constant w.r.t. y"
    -- x is not relatively constant w.r.t. [x]
    guard (!isRelativelyConstant x #[x.fvarId!]) <|>
      throwError "x should not be relatively constant w.r.t. x"

#eval testIsConstantTrue
#eval testIsConstantFalse
#eval testIsRelativelyConstant

end ConstantDetection

/-! ## Beta Reduction Tests -/

section BetaReduction

/-- Test: `mkAppBeta` performs beta reduction. -/
def testMkAppBeta : MetaM Unit := do
  -- Create λ x. x
  let lam := mkLambda `x .default (mkConst ``Nat) (mkBVar 0)
  let arg := mkConst ``Nat.zero
  let result := mkAppBeta lam arg
  -- Should be: Nat.zero
  guard (result.isConstOf ``Nat.zero) <|> throwError "Expected Nat.zero after beta reduction"

/-- Test: `mkAppNBeta` performs multiple beta reductions. -/
def testMkAppNBeta : MetaM Unit := do
  -- Create λ x y. x
  let lam := mkLambda `x .default (mkConst ``Nat)
    (mkLambda `y .default (mkConst ``Nat) (mkBVar 1))
  let result := mkAppNBeta lam #[mkConst ``Nat.zero, mkConst ``Nat.zero]
  -- Should be: Nat.zero (the first argument)
  guard (result.isConstOf ``Nat.zero) <|> throwError "Expected Nat.zero after beta reduction"

#eval testMkAppBeta
#eval testMkAppNBeta

end BetaReduction

/-! ## Expression Size Tests -/

section ExprSize

/-- Test: `size` returns correct size for constants. -/
def testSizeConst : MetaM Unit := do
  let e := mkConst ``Nat
  guard (size e == 1) <|> throwError "Constant should have size 1"

/-- Test: `size` returns correct size for applications. -/
def testSizeApp : MetaM Unit := do
  let e := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
  guard (size e == 2) <|> throwError "App should have size 2"

/-- Test: `size` returns correct size for lambdas. -/
def testSizeLambda : MetaM Unit := do
  let e := mkLambda `x .default (mkConst ``Nat) (mkBVar 0)
  guard (size e == 2) <|> throwError "Lambda should have size 2"

#eval testSizeConst
#eval testSizeApp
#eval testSizeLambda

end ExprSize

/-! ## Array Construction Tests -/

section ArrayConstruction

/-- Test: `mkArray` creates Array expression. -/
def testMkArray : MetaM Unit := do
  let nat := mkConst ``Nat
  let zero := mkConst ``Nat.zero
  let result ← mkArray nat #[zero, zero]
  -- Should be: Array.push (Array.push Array.empty 0) 0
  guard (result.isAppOf ``Array.push) <|> throwError "Expected Array.push"

/-- Test: `mkArray` with empty array. -/
def testMkArrayEmpty : MetaM Unit := do
  let nat := mkConst ``Nat
  let result ← mkArray nat #[]
  guard (result.isAppOf ``Array.empty) <|> throwError "Expected Array.empty"

#eval testMkArray
#eval testMkArrayEmpty

end ArrayConstruction

/-! ## MData Removal Tests -/

section MDataRemoval

/-- Test: `removeMData` strips metadata. -/
def testRemoveMData : MetaM Unit := do
  let e := mkMData {} (mkConst ``Nat)
  let result ← removeMData e
  guard (result.isConstOf ``Nat) <|> throwError "Expected Nat after removing mdata"

#eval testRemoveMData

end MDataRemoval

end CvxLean.Test.Meta.Util.Expr
