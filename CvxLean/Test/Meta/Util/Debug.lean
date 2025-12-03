import CvxLean.Meta.Util.Debug

/-!
# Debug Trace Tests

Tests for `/CvxLean/Meta/Util/Debug.lean` - custom trace classes.
-/

open Lean

-- Test: Trace classes are registered and can be used
set_option trace.CvxLean true in
#check 1

set_option trace.CvxLean.debug true in
#check 2

/-- Test: Trace options exist. -/
def testTraceClassesExist : IO Unit := do
  -- If we got here, the trace classes were registered successfully
  IO.println "Trace classes registered successfully"

#eval testTraceClassesExist
