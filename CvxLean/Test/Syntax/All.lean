import CvxLean.Test.Syntax.Parser
import CvxLean.Test.Syntax.Minimization
import CvxLean.Test.Syntax.Label
import CvxLean.Test.Syntax.Prod
import CvxLean.Test.Syntax.OptimizationParam
import CvxLean.Test.Syntax.Options

/-!
# Syntax Test Suite

Golden Output Testing for the `/CvxLean/Syntax/` infrastructure.

## Philosophy

These tests define **canonical expected behavior** for all syntax operations.
If a test fails, the fault is in the source file, not the test.

## Test Categories

| File | Source | Tests |
|------|--------|-------|
| `Parser.lean` | `Syntax/Parser.lean` | DSL parsing, `optimization` keyword, `minimize`/`maximize`, `subject to` |
| `Minimization.lean` | `Syntax/Minimization.lean` | `term_elab optimization`, delaborator, round-trip |
| `Label.lean` | `Syntax/Label.lean` | `mkLabel`, `decomposeLabel`, label preservation |
| `Prod.lean` | `Syntax/Prod.lean` | `x#n` syntax, `elabProdField`, `delabProdField` |
| `OptimizationParam.lean` | `Syntax/OptimizationParam.lean` | `@[optimization_param]` attribute |
| `Options.lean` | `Syntax/Options.lean` | Pretty-printing options |

## Running Tests

```bash
lake env lean CvxLean/Test/Syntax/All.lean
```
-/
