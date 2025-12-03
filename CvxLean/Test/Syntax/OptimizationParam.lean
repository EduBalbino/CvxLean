import CvxLean.Syntax.OptimizationParam

/-!
# Golden Tests for Syntax/OptimizationParam.lean

Tests the `@[optimization_param]` attribute system:
- `optimizationParamAttr` registration
- `isOptimizationParam` detection
- `getAllOptimizationParams` enumeration
- `getOptimizationParamExpr` value extraction

## Golden Behavior

Definitions tagged with `@[optimization_param]` should be:
1. Detectable via `isOptimizationParam`
2. Listed in `getAllOptimizationParams`
3. Have their values extractable via `getOptimizationParamExpr`
-/

namespace CvxLean.Test.Syntax.OptimizationParam

open Lean Meta

/-! ## Golden Definitions -/

section GoldenDefinitions

/-- GOLDEN: Tagged optimization parameter. -/
@[optimization_param] def goldenParam1 : Nat := 42

/-- GOLDEN: Another tagged parameter. -/
@[optimization_param] def goldenParam2 : Nat := 100

/-- GOLDEN: Not a parameter (no attribute). -/
def notAParam : Nat := 999

end GoldenDefinitions

/-! ## Attribute Detection Tests -/

section AttributeDetection

/-- Test: Tagged definition is detected as optimization_param. -/
def test_isOptimizationParam_tagged : MetaM Unit := do
  let result ← isOptimizationParam ``goldenParam1
  guard result <|> throwError "GOLDEN VIOLATION: goldenParam1 should be an optimization_param"

/-- Test: Second tagged definition is also detected. -/
def test_isOptimizationParam_tagged2 : MetaM Unit := do
  let result ← isOptimizationParam ``goldenParam2
  guard result <|> throwError "GOLDEN VIOLATION: goldenParam2 should be an optimization_param"

/-- Test: Untagged definition is NOT detected as optimization_param. -/
def test_isOptimizationParam_untagged : MetaM Unit := do
  let result ← isOptimizationParam ``notAParam
  guard (!result) <|> throwError "GOLDEN VIOLATION: notAParam should NOT be an optimization_param"

/-- Test: Random name is NOT an optimization_param. -/
def test_isOptimizationParam_nonexistent : MetaM Unit := do
  let result ← isOptimizationParam `nonExistentName
  guard (!result) <|> throwError "GOLDEN VIOLATION: nonExistentName should NOT be an optimization_param"

#eval test_isOptimizationParam_tagged
#eval test_isOptimizationParam_tagged2
#eval test_isOptimizationParam_untagged
#eval test_isOptimizationParam_nonexistent

end AttributeDetection

/-! ## Enumeration Tests -/

section Enumeration

/-- Test: getAllOptimizationParams includes tagged definitions. -/
def test_getAllOptimizationParams_includes_tagged : MetaM Unit := do
  let params ← getAllOptimizationParams
  guard (params.contains ``goldenParam1) <|>
    throwError "GOLDEN VIOLATION: getAllOptimizationParams should include goldenParam1"
  guard (params.contains ``goldenParam2) <|>
    throwError "GOLDEN VIOLATION: getAllOptimizationParams should include goldenParam2"

/-- Test: getAllOptimizationParams excludes untagged definitions. -/
def test_getAllOptimizationParams_excludes_untagged : MetaM Unit := do
  let params ← getAllOptimizationParams
  guard (!params.contains ``notAParam) <|>
    throwError "GOLDEN VIOLATION: getAllOptimizationParams should NOT include notAParam"

#eval test_getAllOptimizationParams_includes_tagged
#eval test_getAllOptimizationParams_excludes_untagged

end Enumeration

/-! ## Value Extraction Tests -/

section ValueExtraction

/-- Test: getOptimizationParamExpr extracts definition value. -/
def test_getOptimizationParamExpr : MetaM Unit := do
  -- Create a placeholder expression
  let placeholder := mkNatLit 0
  let value ← getOptimizationParamExpr ``goldenParam1 placeholder
  -- The extracted value should be the literal 42
  guard (value == mkNatLit 42) <|>
    throwError "GOLDEN VIOLATION: getOptimizationParamExpr should return 42, got {value}"

/-- Test: getOptimizationParamExpr works for second param. -/
def test_getOptimizationParamExpr2 : MetaM Unit := do
  let placeholder := mkNatLit 0
  let value ← getOptimizationParamExpr ``goldenParam2 placeholder
  guard (value == mkNatLit 100) <|>
    throwError "GOLDEN VIOLATION: getOptimizationParamExpr should return 100, got {value}"

#eval test_getOptimizationParamExpr
#eval test_getOptimizationParamExpr2

end ValueExtraction

/-! ## Attribute Registration Tests -/

section AttributeRegistration

/-- Test: optimizationParamAttr is properly registered. -/
def test_attribute_registered : MetaM Unit := do
  -- Just verify we can access the attribute without error
  let env ← getEnv
  let _ := optimizationParamAttr.hasTag env ``goldenParam1
  pure ()

#eval test_attribute_registered

end AttributeRegistration

end CvxLean.Test.Syntax.OptimizationParam
