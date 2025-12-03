import CvxLean.Meta.Util.Error

/-!
# Error Macro Tests

Tests for `/CvxLean/Meta/Util/Error.lean` - custom error message macros.

These macros are syntax-only (they expand to `throwError`), so we just verify
they parse and expand correctly.
-/

open Lean

-- Test: All error macros parse correctly (syntax check)
-- We use `#check` on lambdas to verify the syntax is valid

/-- Test: throwParserError parses with interpolated string. -/
def testParserError : MetaM Unit := do
  try throwParserError "test message"
  catch _ => pure ()

/-- Test: throwTacticBuilderError parses. -/
def testTacticBuilderError : MetaM Unit := do
  try throwTacticBuilderError "test"
  catch _ => pure ()

/-- Test: throwDCPError parses. -/
def testDCPError : MetaM Unit := do
  try throwDCPError "test"
  catch _ => pure ()

/-- Test: throwSolveError parses. -/
def testSolveError : MetaM Unit := do
  try throwSolveError "test"
  catch _ => pure ()

/-- Test: throwEquivalenceError parses. -/
def testEquivalenceError : MetaM Unit := do
  try throwEquivalenceError "test"
  catch _ => pure ()

/-- Test: throwReductionError parses. -/
def testReductionError : MetaM Unit := do
  try throwReductionError "test"
  catch _ => pure ()

/-- Test: throwRelaxationError parses. -/
def testRelaxationError : MetaM Unit := do
  try throwRelaxationError "test"
  catch _ => pure ()

/-- Test: throwCoeffsError parses. -/
def testCoeffsError : MetaM Unit := do
  try throwCoeffsError "test"
  catch _ => pure ()

/-- Test: throwAtomDeclarationError parses. -/
def testAtomDeclarationError : MetaM Unit := do
  try throwAtomDeclarationError "test"
  catch _ => pure ()

-- Run all tests
#eval testParserError
#eval testTacticBuilderError
#eval testDCPError
#eval testSolveError
#eval testEquivalenceError
#eval testReductionError
#eval testRelaxationError
#eval testCoeffsError
#eval testAtomDeclarationError
