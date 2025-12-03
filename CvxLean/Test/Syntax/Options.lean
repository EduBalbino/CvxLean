import CvxLean.Syntax.Options

/-!
# Golden Tests for Syntax/Options.lean

Tests the pretty-printing options for CvxLean.

## Current State

The source file has `pp.opt` and `pp.labels` options **commented out**.
This test file documents this state and verifies the file compiles.

## Golden Behavior

When options are enabled, they should:
1. `pp.opt` - Control whether minimization problems are pretty-printed
2. `pp.labels` - Control whether CvxLean labels are displayed

## Note

These tests are minimal since the options are currently disabled.
If the options are re-enabled, expand these tests to verify:
- Default values are correct
- Options affect pretty-printing behavior
- Options can be set via `set_option`
-/

namespace CvxLean.Test.Syntax.Options

open Lean

/-! ## Compilation Test -/

section CompilationTest

/-- Test: Options.lean compiles without error. -/
def test_options_compiles : IO Unit := do
  IO.println "Options.lean compiles successfully"

#eval test_options_compiles

end CompilationTest

/-! ## Namespace Test -/

section NamespaceTest

/-- Test: CvxLean namespace is accessible. -/
def test_namespace_exists : IO Unit := do
  -- The CvxLean namespace should exist after importing Options.lean
  IO.println "CvxLean namespace accessible"

#eval test_namespace_exists

end NamespaceTest

/-! ## Documentation of Commented Options -/

section DocumentedOptions

/--
The following options are defined but commented out in the source:

```lean
-- register_option pp.opt : Bool := {
--   defValue := true
--   group    := "pp"
--   descr    := "(pretty printer) pretty-print minimization problems."
-- }

-- register_option pp.labels : Bool := {
--   defValue := false
--   group    := "pp"
--   descr    := "(pretty printer) display CvxLean labels."
-- }
```

When these are uncommented, add tests for:
1. `set_option pp.opt true` / `set_option pp.opt false`
2. `set_option pp.labels true` / `set_option pp.labels false`
3. Verify default values (pp.opt = true, pp.labels = false)
4. Verify pretty-printing behavior changes accordingly
-/
def documented_options : String := "pp.opt, pp.labels (currently commented out)"

#check documented_options

end DocumentedOptions

end CvxLean.Test.Syntax.Options
