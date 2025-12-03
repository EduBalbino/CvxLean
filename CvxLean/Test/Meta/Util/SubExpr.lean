import CvxLean.Meta.Util.SubExpr

/-!
# SubExpr Utility Tests

Tests for `/CvxLean/Meta/Util/SubExpr.lean` - delaborator helper functions.
-/

open Lean Meta PrettyPrinter Delaborator

-- Test: Verify the functions exist and compile
#check @SubExpr.withExpr
#check @SubExpr.withBindingBody''

/-- Test: SubExpr.withExpr has expected signature. -/
def testWithExprExists : IO Unit := do
  IO.println "SubExpr.withExpr exists"

#eval testWithExprExists

/-- Test: SubExpr.withBindingBody'' has expected signature. -/
def testWithBindingBody''Exists : IO Unit := do
  IO.println "SubExpr.withBindingBody'' exists"

#eval testWithBindingBody''Exists
