import CvxLean.Test.Meta.Attributes
import CvxLean.Test.Meta.Minimization
import CvxLean.Test.Meta.Equivalence
import CvxLean.Test.Meta.Reduction
import CvxLean.Test.Meta.Relaxation
import CvxLean.Test.Meta.TacticBuilder
import CvxLean.Test.Meta.Util.All

/-!
# Meta Infrastructure Test Suite

Golden Output Testing for the `/CvxLean/Meta/` infrastructure.

## Philosophy

These tests use **Golden Output Testing**: we define canonical optimization problems
and assert that Meta operations produce expected outputs. Tests fail when behavior
changes, serving as regression detection for the Mathlib migration.

## Test Categories

| File | Tests |
|------|-------|
| `Minimization.lean` | Domain/constraint decomposition, projections |
| `Equivalence.lean` | `EquivalenceExpr` parsing and construction |
| `TacticBuilder.lean` | Builder-to-tactic conversion, goal handling |
| `Util/` | Expression utilities, error macros, ToExpr |

## Running Tests

```bash
lake env lean CvxLean/Test/Meta/All.lean
```
-/
