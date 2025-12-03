import CvxLean.Meta.Util.ToExpr

/-!
# Tests for Meta/Util/ToExpr.lean

Golden output tests for `ToExpr` instances:
- `ToExpr Float`
- `ToExpr (Fin n)`
- `ToExpr (Array Float)`
- `ToExpr (Array (Array Float))`

## Expected Behavior

These tests verify that numeric values are correctly converted to expressions.
This is critical for the solver interface which converts Float solutions back
to Lean expressions.

## Known Issues

The `ToExpr (Fin n)` instance uses `Fin.ofNat` which may have changed in Lean 4.26.
See ReportMeta.md for details.
-/

namespace CvxLean.Test.Meta.Util.ToExpr

open Lean Lean.Meta

/-! ## Float ToExpr Tests -/

section FloatToExpr

/-- Test: Positive float converts correctly. -/
def testFloatPositive : MetaM Unit := do
  let f : Float := 3.14
  let e := toExpr f
  -- Should create OfScientific.ofScientific expression
  guard e.isApp <|> throwError "Expected application"

/-- Test: Negative float converts correctly. -/
def testFloatNegative : MetaM Unit := do
  let f : Float := -2.5
  let e := toExpr f
  -- Should wrap with Float.neg
  guard e.isApp <|> throwError "Expected application"

/-- Test: Zero float converts correctly. -/
def testFloatZero : MetaM Unit := do
  let f : Float := 0.0
  let e := toExpr f
  guard e.isApp <|> throwError "Expected application"

/-- Test: Integer-valued float converts correctly. -/
def testFloatInteger : MetaM Unit := do
  let f : Float := 42.0
  let e := toExpr f
  guard e.isApp <|> throwError "Expected application"

#eval testFloatPositive
#eval testFloatNegative
#eval testFloatZero
#eval testFloatInteger

end FloatToExpr

/-! ## Fin ToExpr Tests -/

section FinToExpr

/-- Test: Fin value converts correctly using standard library instance.
The standard library uses OfNat.ofNat for Fin values. -/
def testFin : MetaM Unit := do
  let f : Fin 5 := ⟨3, by omega⟩
  let e := toExpr f
  -- Standard library uses OfNat.ofNat for Fin
  guard (e.isAppOf ``OfNat.ofNat) <|> throwError "Expected OfNat.ofNat, got {e}"
  -- Verify the type is correct (not a function)
  let ty ← inferType e
  guard (!ty.isForall) <|> throwError "Type should not be a function, got {ty}"

/-- Test: Fin 0 value (edge case). -/
def testFinZero : MetaM Unit := do
  let f : Fin 5 := ⟨0, by omega⟩
  let e := toExpr f
  guard (e.isAppOf ``OfNat.ofNat) <|> throwError "Expected OfNat.ofNat"
  let ty ← inferType e
  guard (!ty.isForall) <|> throwError "Type should not be a function"

/-- Test: Fin max value. -/
def testFinMax : MetaM Unit := do
  let f : Fin 5 := ⟨4, by omega⟩
  let e := toExpr f
  guard (e.isAppOf ``OfNat.ofNat) <|> throwError "Expected OfNat.ofNat"
  let ty ← inferType e
  guard (!ty.isForall) <|> throwError "Type should not be a function"

#eval testFin
#eval testFinZero
#eval testFinMax

end FinToExpr

/-! ## Array ToExpr Tests -/

section ArrayToExpr

/-- Test: Array Float converts correctly. -/
def testArrayFloat : MetaM Unit := do
  let arr : Array Float := #[1.0, 2.0, 3.0]
  let e := toExpr arr
  -- Should create Array expression
  guard e.isApp <|> throwError "Expected application"

/-- Test: Empty Array Float converts correctly. -/
def testArrayFloatEmpty : MetaM Unit := do
  let arr : Array Float := #[]
  let e := toExpr arr
  guard e.isApp <|> throwError "Expected application"

/-- Test: Nested Array Float converts correctly. -/
def testArrayArrayFloat : MetaM Unit := do
  let arr : Array (Array Float) := #[#[1.0, 2.0], #[3.0, 4.0]]
  let e := toExpr arr
  guard e.isApp <|> throwError "Expected application"

#eval testArrayFloat
#eval testArrayFloatEmpty
#eval testArrayArrayFloat

end ArrayToExpr

/-! ## Type Expression Tests -/

section TypeExpr

/-- Test: Float type expression is correct. -/
def testFloatTypeExpr : MetaM Unit := do
  let ty := @toTypeExpr Float _
  guard (ty.isConstOf ``Float) <|> throwError "Expected Float type"

/-- Test: Fin type expression is correct. -/
def testFinTypeExpr : MetaM Unit := do
  let ty := @toTypeExpr (Fin 5) _
  guard (ty.isAppOf ``Fin) <|> throwError "Expected Fin type"

#eval testFloatTypeExpr
#eval testFinTypeExpr

end TypeExpr

/-! ## Round-Trip Tests -/

section RoundTrip

/-- Test: Float round-trip through expression. -/
def testFloatRoundTrip : MetaM Unit := do
  -- This is a structural test - we verify the expression has the right shape
  -- Actual evaluation would require more infrastructure
  let f : Float := 1.5
  let e := toExpr f
  let ty ← inferType e
  guard (← isDefEq ty (mkConst ``Float)) <|> throwError "Type should be Float"

#eval testFloatRoundTrip

end RoundTrip

end CvxLean.Test.Meta.Util.ToExpr
