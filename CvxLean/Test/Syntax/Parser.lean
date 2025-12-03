import CvxLean.Syntax.Parser
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Lib.Minimization
import Mathlib.Data.Real.Basic

/-!
# Golden Tests for Syntax/Parser.lean

Tests the `optimization` DSL parsing infrastructure:
- `minimizationVar` syntax category
- `letVar` syntax category
- `constraint` syntax category
- `minOrMax` syntax category
- Full `optimization` syntax

## Golden Behavior

The parser MUST:
1. Accept all valid optimization syntax forms
2. Reject malformed syntax with clear errors
3. Handle indentation correctly for constraints
4. Support both `minimize` and `maximize` keywords
-/

namespace CvxLean.Test.Syntax.Parser

open Lean Lean.Meta CvxLean CvxLean.Meta

/-! ## Helper to get expression from constant -/

def getConstExpr (n : Name) : MetaM Expr := do
  match (← getEnv).constants.find! n with
  | ConstantInfo.defnInfo defn => return defn.value
  | _ => throwError "Not a definition: {n}"

/-! ## Golden Test Problems

These are canonical optimization problems that MUST parse correctly. -/

section GoldenProblems

/-- GOLDEN: Single variable, minimize, no constraints. -/
def golden_single_var_min := optimization (x : ℝ)
  minimize x

/-- GOLDEN: Single variable, maximize, no constraints. -/
def golden_single_var_max := optimization (x : ℝ)
  maximize x

/-- GOLDEN: Two variables, minimize, no constraints. -/
def golden_two_vars := optimization (x y : ℝ)
  minimize x + y

/-- GOLDEN: Three variables with separate declarations. -/
def golden_three_vars_separate := optimization (x : ℝ) (y : ℝ) (z : ℝ)
  minimize x + y + z

/-- GOLDEN: Mixed variable declarations. -/
def golden_mixed_decls := optimization (x y : ℝ) (z : ℝ)
  minimize x + y + z

/-- GOLDEN: Single constraint. -/
def golden_single_constr := optimization (x : ℝ)
  minimize x
  subject to
    h : 0 ≤ x

/-- GOLDEN: Multiple constraints. -/
def golden_multi_constr := optimization (x y : ℝ)
  minimize x + y
  subject to
    h₁ : 0 ≤ x
    h₂ : 0 ≤ y
    h₃ : x ≤ y

/-- GOLDEN: Anonymous constraint (underscore). -/
def golden_anon_constr := optimization (x : ℝ)
  minimize x
  subject to
    _ : 0 ≤ x

/-- GOLDEN: Mixed named and anonymous constraints. -/
def golden_mixed_constrs := optimization (x y : ℝ)
  minimize x + y
  subject to
    h₁ : 0 ≤ x
    _ : 0 ≤ y
    h₃ : x ≤ 1

/-- GOLDEN: Maximize with constraints. -/
def golden_maximize_constrs := optimization (x y : ℝ)
  maximize x + y
  subject to
    h₁ : x ≤ 10
    h₂ : y ≤ 10

/-- GOLDEN: Let binding in optimization. -/
def golden_let_binding := optimization (x y : ℝ)
  with z := x + y
  minimize z^2
  subject to
    h : z ≤ 1

end GoldenProblems

/-! ## Parser Acceptance Tests

Verify that all golden problems parse to valid `Minimization` expressions. -/

section AcceptanceTests

/-- Test: Single variable problem parses correctly. -/
def test_parse_single_var : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_single_var_min)
  let vars ← decomposeDomain minExpr.domain
  guard (vars.length == 1) <|> throwError "GOLDEN VIOLATION: Expected 1 variable"
  guard (vars[0]!.1 == `x) <|> throwError "GOLDEN VIOLATION: Expected variable name `x`"

/-- Test: Two variable problem parses correctly. -/
def test_parse_two_vars : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_two_vars)
  let vars ← decomposeDomain minExpr.domain
  guard (vars.length == 2) <|> throwError "GOLDEN VIOLATION: Expected 2 variables"
  guard (vars[0]!.1 == `x) <|> throwError "GOLDEN VIOLATION: Expected first variable `x`"
  guard (vars[1]!.1 == `y) <|> throwError "GOLDEN VIOLATION: Expected second variable `y`"

/-- Test: Three variables with separate declarations parse correctly. -/
def test_parse_three_vars : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_three_vars_separate)
  let vars ← decomposeDomain minExpr.domain
  guard (vars.length == 3) <|> throwError "GOLDEN VIOLATION: Expected 3 variables"
  guard (vars[0]!.1 == `x) <|> throwError "GOLDEN VIOLATION: Expected `x`"
  guard (vars[1]!.1 == `y) <|> throwError "GOLDEN VIOLATION: Expected `y`"
  guard (vars[2]!.1 == `z) <|> throwError "GOLDEN VIOLATION: Expected `z`"

/-- Test: Single constraint parses with correct label. -/
def test_parse_single_constr : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_single_constr)
  let constrs ← decomposeConstraints minExpr.constraints.bindingBody!
  guard (constrs.length == 1) <|> throwError "GOLDEN VIOLATION: Expected 1 constraint"
  guard (constrs[0]!.1 == `h) <|> throwError "GOLDEN VIOLATION: Expected constraint label `h`"

/-- Test: Multiple constraints parse with correct labels. -/
def test_parse_multi_constr : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_multi_constr)
  let constrs ← decomposeConstraints minExpr.constraints.bindingBody!
  guard (constrs.length == 3) <|> throwError "GOLDEN VIOLATION: Expected 3 constraints"
  guard (constrs[0]!.1 == `h₁) <|> throwError "GOLDEN VIOLATION: Expected `h₁`"
  guard (constrs[1]!.1 == `h₂) <|> throwError "GOLDEN VIOLATION: Expected `h₂`"
  guard (constrs[2]!.1 == `h₃) <|> throwError "GOLDEN VIOLATION: Expected `h₃`"

/-- Test: Anonymous constraint has anonymous name. -/
def test_parse_anon_constr : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_anon_constr)
  let constrs ← decomposeConstraints minExpr.constraints.bindingBody!
  guard (constrs.length == 1) <|> throwError "GOLDEN VIOLATION: Expected 1 constraint"
  guard (constrs[0]!.1 == Name.anonymous) <|>
    throwError "GOLDEN VIOLATION: Expected anonymous constraint name"

/-- Test: Maximize keyword is recognized. -/
def test_parse_maximize : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_single_var_max)
  let objBody := minExpr.objFun.bindingBody!
  guard (objBody.isAppOf ``maximizeNeg) <|>
    throwError "GOLDEN VIOLATION: Maximize should use `maximizeNeg` wrapper"

/-- Test: Let bindings are incorporated. -/
def test_parse_let_binding : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_let_binding)
  let objBody := minExpr.objFun.bindingBody!
  guard objBody.isLet <|>
    throwError "GOLDEN VIOLATION: Let binding should appear in objective"

#eval test_parse_single_var
#eval test_parse_two_vars
#eval test_parse_three_vars
#eval test_parse_single_constr
#eval test_parse_multi_constr
#eval test_parse_anon_constr
#eval test_parse_maximize
#eval test_parse_let_binding

end AcceptanceTests

/-! ## Syntax Category Tests

Verify individual syntax categories work correctly. -/

section SyntaxCategories

/-- Test: `minimizationVar` accepts identifier. -/
def test_minimizationVar_ident : MetaM Unit := do
  -- This compiles means the syntax is accepted
  let _ := optimization (x : ℝ) minimize x
  return ()

/-- Test: `minimizationVar` accepts bracketed binder. -/
def test_minimizationVar_bracketed : MetaM Unit := do
  let _ := optimization (x y z : ℝ) minimize x + y + z
  return ()

/-- Test: `constraint` syntax with identifier. -/
def test_constraint_ident : MetaM Unit := do
  let _ := optimization (x : ℝ) minimize x subject to myConstr : 0 ≤ x
  return ()

/-- Test: `constraint` syntax with underscore. -/
def test_constraint_anon : MetaM Unit := do
  let _ := optimization (x : ℝ) minimize x subject to _ : 0 ≤ x
  return ()

#eval test_minimizationVar_ident
#eval test_minimizationVar_bracketed
#eval test_constraint_ident
#eval test_constraint_anon

end SyntaxCategories

/-! ## Edge Cases

Test boundary conditions and special cases. -/

section EdgeCases

/-- GOLDEN: Problem with no constraints (implicit True). -/
def golden_no_constrs := optimization (x : ℝ)
  minimize x

/-- Test: No constraints elaborates to True. -/
def test_no_constrs_is_true : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_no_constrs)
  let constraintBody := minExpr.constraints.bindingBody!
  guard (← isDefEq constraintBody (mkConst ``True)) <|>
    throwError "GOLDEN VIOLATION: No constraints should elaborate to True"

/-- GOLDEN: Unicode constraint names. -/
def golden_unicode_names := optimization (x : ℝ)
  minimize x
  subject to
    α : 0 ≤ x
    β : x ≤ 1

/-- Test: Unicode constraint names are preserved. -/
def test_unicode_names : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_unicode_names)
  let constrs ← decomposeConstraints minExpr.constraints.bindingBody!
  guard (constrs[0]!.1 == `α) <|> throwError "GOLDEN VIOLATION: Expected `α`"
  guard (constrs[1]!.1 == `β) <|> throwError "GOLDEN VIOLATION: Expected `β`"

/-- GOLDEN: Subscript names. -/
def golden_subscript_names := optimization (x₁ x₂ : ℝ)
  minimize x₁ + x₂
  subject to
    h₁ : 0 ≤ x₁
    h₂ : 0 ≤ x₂

/-- Test: Subscript variable names are preserved. -/
def test_subscript_names : MetaM Unit := do
  let minExpr ← MinimizationExpr.fromExpr (← getConstExpr ``golden_subscript_names)
  let vars ← decomposeDomain minExpr.domain
  guard (vars[0]!.1 == `x₁) <|> throwError "GOLDEN VIOLATION: Expected `x₁`"
  guard (vars[1]!.1 == `x₂) <|> throwError "GOLDEN VIOLATION: Expected `x₂`"

#eval test_no_constrs_is_true
#eval test_unicode_names
#eval test_subscript_names

end EdgeCases

end CvxLean.Test.Syntax.Parser
