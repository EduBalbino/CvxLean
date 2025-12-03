import CvxLean.Meta.Util.Simp

/-!
# Simp Configuration Tests

Tests for `/CvxLean/Meta/Util/Simp.lean` - custom simp configuration.
-/

open Lean Meta

/-- Test: aggressiveSimpConfig has expected settings. -/
def testAggressiveSimpConfig : MetaM Unit := do
  guard aggressiveSimpConfig.zeta <|>
    throwError "Expected zeta = true"
  guard aggressiveSimpConfig.beta <|>
    throwError "Expected beta = true"
  guard aggressiveSimpConfig.eta <|>
    throwError "Expected eta = true"
  guard aggressiveSimpConfig.iota <|>
    throwError "Expected iota = true"
  guard aggressiveSimpConfig.proj <|>
    throwError "Expected proj = true"
  guard aggressiveSimpConfig.decide <|>
    throwError "Expected decide = true"
  guard aggressiveSimpConfig.arith <|>
    throwError "Expected arith = true"
  guard aggressiveSimpConfig.dsimp <|>
    throwError "Expected dsimp = true"
  guard aggressiveSimpConfig.unfoldPartialApp <|>
    throwError "Expected unfoldPartialApp = true"
  guard (aggressiveSimpConfig.etaStruct == .all) <|>
    throwError "Expected etaStruct = .all"

#eval testAggressiveSimpConfig

/-- Test: aggressiveSimpConfig can be used in simp. -/
def testSimpWithConfig : MetaM Unit := do
  -- Just verify the config is valid for simp
  let ctx ← Simp.mkContext aggressiveSimpConfig
  guard (ctx.config.zeta) <|> throwError "Config not applied correctly"

#eval testSimpWithConfig
