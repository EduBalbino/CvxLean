import CvxLean.Meta.Util.Meta

/-!
# Meta Utility Tests

Tests for `/CvxLean/Meta/Util/Meta.lean` - helper Meta functions.
-/

open Lean Meta Elab Tactic Term

/-- Test: withLambdaBody opens a lambda expression. -/
def testWithLambdaBody : MetaM Unit := do
  -- Create λ x : Nat, x + 1
  let lam ← withLocalDeclD `x (Lean.mkConst ``Nat) fun x => do
    let body := mkApp2 (Lean.mkConst ``Nat.add) x (mkNatLit 1)
    mkLambdaFVars #[x] body
  withLambdaBody lam fun fvar body => do
    guard fvar.isFVar <|> throwError "Expected fvar"
    guard (body.isApp) <|> throwError "Expected application in body"

#eval testWithLambdaBody

/-- Test: withLambdaBody rejects non-lambda. -/
def testWithLambdaBodyRejectsNonLambda : MetaM Unit := do
  try
    withLambdaBody (Lean.mkConst ``Nat) fun _ _ => pure ()
    throwError "Should have rejected non-lambda"
  catch _ =>
    pure ()

#eval testWithLambdaBodyRejectsNonLambda

/-- Test: withLocalDeclsDNondep introduces multiple declarations. -/
def testWithLocalDeclsDNondep : MetaM Unit := do
  let declInfos := #[(`x, Lean.mkConst ``Nat), (`y, Lean.mkConst ``Nat)]
  withLocalDeclsDNondep declInfos fun xs => do
    guard (xs.size == 2) <|> throwError "Expected 2 fvars"
    guard xs[0]!.isFVar <|> throwError "Expected fvar at index 0"
    guard xs[1]!.isFVar <|> throwError "Expected fvar at index 1"

#eval testWithLocalDeclsDNondep

/-- Test: withLetDecls introduces let declarations. -/
def testWithLetDecls : MetaM Unit := do
  let declInfos : Array (Name × (Array Expr → MetaM Expr) × (Array Expr → MetaM Expr)) := #[
    (`x, fun _ => pure (Lean.mkConst ``Nat), fun _ => pure (mkNatLit 42))
  ]
  withLetDecls declInfos fun xs => do
    guard (xs.size == 1) <|> throwError "Expected 1 let binding"
    guard xs[0]!.isFVar <|> throwError "Expected fvar"

#eval testWithLetDecls

/-- Test: runTactic executes a tactic on a goal. -/
def testRunTactic : MetaM Unit := do
  -- Create a trivial goal: True
  let goal ← mkFreshExprMVar (Lean.mkConst ``True)
  let mvarId := goal.mvarId!
  let remaining ← runTactic mvarId fun g => do
    g.assign (Lean.mkConst ``True.intro)
    return []
  guard (remaining.isEmpty) <|> throwError "Expected no remaining goals"

#eval testRunTactic
