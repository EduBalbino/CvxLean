import CvxLean.Syntax.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Lib.Minimization
import Mathlib.Data.Real.Basic

/-!
# Golden Tests for Syntax/Minimization.lean

Tests the `optimization` elaboration and delaboration:
- `elabOptmiziation` term elaborator
- `delabMinimization` delaborator
- Round-trip preservation
- `maximizeNeg` handling

## Golden Behavior

The elaborator MUST:
1. Build correct `Minimization.mk` terms
2. Preserve variable names in domain labels
3. Preserve constraint names in constraint labels
4. Wrap maximize objectives with `maximizeNeg`
5. Handle let bindings correctly

The delaborator MUST:
1. Reconstruct valid `optimization` syntax
2. Preserve variable names
3. Preserve constraint labels
4. Distinguish minimize/maximize
-/

namespace CvxLean.Test.Syntax.Minimization

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.PrettyPrinter CvxLean CvxLean.Meta

/-! ## Golden Test Problems

These compile-time definitions verify the syntax is valid. -/

section GoldenProblems

/-- GOLDEN: Simplest problem. -/
def golden_simplest := optimization (x : ℝ)
  minimize x

/-- GOLDEN: Two variables. -/
def golden_two_vars := optimization (x y : ℝ)
  minimize x + y

/-- GOLDEN: With constraints. -/
def golden_with_constrs := optimization (x y : ℝ)
  minimize x + y
  subject to
    h₁ : 0 ≤ x
    h₂ : 0 ≤ y

/-- GOLDEN: Maximize problem. -/
def golden_maximize := optimization (x : ℝ)
  maximize x
  subject to
    h : x ≤ 10

/-- GOLDEN: Complex expressions. -/
def golden_complex := optimization (x y z : ℝ)
  minimize x^2 + y^2 + z^2
  subject to
    c₁ : x + y + z = 1
    c₂ : 0 ≤ x
    c₃ : 0 ≤ y
    c₄ : 0 ≤ z

end GoldenProblems

-- Verify all golden problems have correct type (outside section to avoid forward reference)
#check (golden_simplest : Minimization ℝ ℝ)
#check (golden_two_vars : Minimization (ℝ × ℝ) ℝ)
#check (golden_with_constrs : Minimization (ℝ × ℝ) ℝ)
#check (golden_maximize : Minimization ℝ ℝ)
#check (golden_complex : Minimization (ℝ × ℝ × ℝ) ℝ)

/-! ## Helper to get expression from constant -/

/-- Get the definition value of a constant. -/
def getConstExpr (n : Name) : MetaM Expr := do
  match (← getEnv).constants.find! n with
  | ConstantInfo.defnInfo defn => return defn.value
  | _ => throwError "Not a definition: {n}"

/-! ## Elaboration Tests

Verify `elabOptmiziation` produces correct `Minimization.mk` terms. -/

section ElaborationTests

/-- Test: Elaboration produces Minimization.mk. -/
def test_elab_produces_minimization_mk : MetaM Unit := do
  let e ← getConstExpr ``golden_simplest
  guard (e.isAppOf ``Minimization.mk) <|>
    throwError "GOLDEN VIOLATION: Should elaborate to Minimization.mk, got {e}"

/-- Test: Domain type is correct for single variable. -/
def test_elab_domain_single : MetaM Unit := do
  let e ← getConstExpr ``golden_simplest
  let minExpr ← MinimizationExpr.fromExpr e
  -- Domain should be ℝ (with label)
  let vars ← decomposeDomain minExpr.domain
  guard (vars.length == 1) <|> throwError "GOLDEN VIOLATION: Expected 1 domain variable"
  let (name, _ty) := vars[0]!
  guard (name == `x) <|> throwError "GOLDEN VIOLATION: Expected name `x`, got {name}"

/-- Test: Domain type is Prod for two variables. -/
def test_elab_domain_prod : MetaM Unit := do
  let e ← getConstExpr ``golden_two_vars
  let minExpr ← MinimizationExpr.fromExpr e
  -- Domain should be ℝ × ℝ
  guard (minExpr.domain.isAppOf ``Prod) <|>
    throwError "GOLDEN VIOLATION: Two variables should have Prod domain"

/-- Test: Objective function is a lambda. -/
def test_elab_objfun_lambda : MetaM Unit := do
  let e ← getConstExpr ``golden_simplest
  let minExpr ← MinimizationExpr.fromExpr e
  guard minExpr.objFun.isLambda <|>
    throwError "GOLDEN VIOLATION: Objective function should be a lambda"

/-- Test: Constraints is a lambda. -/
def test_elab_constrs_lambda : MetaM Unit := do
  let e ← getConstExpr ``golden_with_constrs
  let minExpr ← MinimizationExpr.fromExpr e
  guard minExpr.constraints.isLambda <|>
    throwError "GOLDEN VIOLATION: Constraints should be a lambda"

/-- Test: Maximize uses maximizeNeg wrapper. -/
def test_elab_maximize_neg : MetaM Unit := do
  let e ← getConstExpr ``golden_maximize
  let minExpr ← MinimizationExpr.fromExpr e
  let objBody := minExpr.objFun.bindingBody!
  guard (objBody.isAppOf ``maximizeNeg) <|>
    throwError "GOLDEN VIOLATION: Maximize should wrap with maximizeNeg, got {objBody}"

/-- Test: Constraint labels are preserved in metadata. -/
def test_elab_constraint_labels : MetaM Unit := do
  let e ← getConstExpr ``golden_with_constrs
  let minExpr ← MinimizationExpr.fromExpr e
  let constrs ← decomposeConstraints minExpr.constraints.bindingBody!
  guard (constrs.length == 2) <|> throwError "GOLDEN VIOLATION: Expected 2 constraints, got {constrs.length}"
  guard (constrs[0]!.1 == `h₁) <|> throwError "GOLDEN VIOLATION: First constraint should be `h₁`, got {constrs[0]!.1}"
  guard (constrs[1]!.1 == `h₂) <|> throwError "GOLDEN VIOLATION: Second constraint should be `h₂`, got {constrs[1]!.1}"

/-- Test: Variable labels are preserved in domain. -/
def test_elab_variable_labels : MetaM Unit := do
  let e ← getConstExpr ``golden_two_vars
  let minExpr ← MinimizationExpr.fromExpr e
  let vars ← decomposeDomain minExpr.domain
  guard (vars[0]!.1 == `x) <|> throwError "GOLDEN VIOLATION: First variable should be `x`, got {vars[0]!.1}"
  guard (vars[1]!.1 == `y) <|> throwError "GOLDEN VIOLATION: Second variable should be `y`, got {vars[1]!.1}"

#eval test_elab_produces_minimization_mk
#eval test_elab_domain_single
#eval test_elab_domain_prod
#eval test_elab_objfun_lambda
#eval test_elab_constrs_lambda
#eval test_elab_maximize_neg
#eval test_elab_constraint_labels
#eval test_elab_variable_labels

end ElaborationTests

/-! ## Delaboration Tests

Verify `delabMinimization` produces correct syntax. -/

section DelaborationTests

/-- Test: Delaboration produces optimization syntax. -/
def test_delab_produces_syntax : MetaM Unit := do
  let e ← getConstExpr ``golden_simplest
  let stx ← delab e
  -- The syntax should start with `optimization`
  -- We check by re-elaborating and comparing
  let reElab ← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTerm stx none
  guard (← isDefEq e reElab) <|>
    throwError "GOLDEN VIOLATION: Delaborated syntax should re-elaborate to same expression"

/-- Test: Delaboration preserves variable names. -/
def test_delab_var_names : MetaM Unit := do
  let e ← getConstExpr ``golden_two_vars
  let stx ← delab e
  let reElab ← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTerm stx none
  let minExpr ← MinimizationExpr.fromExpr reElab
  let vars ← decomposeDomain minExpr.domain
  guard (vars[0]!.1 == `x) <|> throwError "GOLDEN VIOLATION: Variable `x` not preserved"
  guard (vars[1]!.1 == `y) <|> throwError "GOLDEN VIOLATION: Variable `y` not preserved"

/-- Test: Delaboration preserves constraint labels. -/
def test_delab_constr_labels : MetaM Unit := do
  let e ← getConstExpr ``golden_with_constrs
  let stx ← delab e
  let reElab ← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTerm stx none
  let minExpr ← MinimizationExpr.fromExpr reElab
  let constrs ← decomposeConstraints minExpr.constraints.bindingBody!
  guard (constrs[0]!.1 == `h₁) <|> throwError "GOLDEN VIOLATION: Constraint `h₁` not preserved"
  guard (constrs[1]!.1 == `h₂) <|> throwError "GOLDEN VIOLATION: Constraint `h₂` not preserved"

#eval test_delab_produces_syntax
#eval test_delab_var_names
#eval test_delab_constr_labels

end DelaborationTests

/-! ## Round-Trip Tests

Verify elab → delab → elab produces equivalent expressions. -/

section RoundTripTests

/-- Test: Round-trip for simple problem. -/
def test_roundtrip_simple : MetaM Unit := do
  let original ← getConstExpr ``golden_simplest
  let stx ← delab original
  let roundTripped ← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTerm stx none
  guard (← isDefEq original roundTripped) <|>
    throwError "GOLDEN VIOLATION: Round-trip failed for simple problem"

/-- Test: Round-trip for two variables. -/
def test_roundtrip_two_vars : MetaM Unit := do
  let original ← getConstExpr ``golden_two_vars
  let stx ← delab original
  let roundTripped ← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTerm stx none
  guard (← isDefEq original roundTripped) <|>
    throwError "GOLDEN VIOLATION: Round-trip failed for two variables"

/-- Diagnostic helper: show exactly what's wrong with round-trip. -/
def diagnoseRoundTrip (name : String) (constName : Name) : MetaM Unit := do
  let original ← getConstExpr constName
  let stx ← delab original

  -- Check constraint syntax nodes if present
  let args := stx.raw.getArgs
  if args.size >= 6 then
    let subjectTo := args[5]!
    if subjectTo.getKind == `null && subjectTo.getArgs.size >= 3 then
      let constrsNode := subjectTo.getArgs[2]!
      if constrsNode.getKind == `null then
        for i in [:constrsNode.getArgs.size] do
          let constr := constrsNode.getArgs[i]!
          let expectedKind := `CvxLean.constraintIdent
          if constr.getKind != expectedKind then
            throwError "DIAGNOSTIC [{name}]: Constraint {i} has kind `{constr.getKind}`, expected `{expectedKind}`\n  Full constraint: {constr}"

  -- Try to re-elaborate
  let roundTripped ← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTerm stx none

  -- Check if it's a sorry (elaboration failed silently)
  if roundTripped.isAppOf ``sorryAx then
    throwError "DIAGNOSTIC [{name}]: Re-elaboration produced sorry!\n  Delaborated syntax kind: {stx.raw.getKind}\n  Syntax: {stx}"

  -- Check definitional equality
  if !(← isDefEq original roundTripped) then
    let origTy ← inferType original
    let rtTy ← inferType roundTripped
    throwError "DIAGNOSTIC [{name}]: Not definitionally equal\n  Original type: {origTy}\n  Round-tripped type: {rtTy}"

/-- Test: Round-trip for problem with constraints. -/
def test_roundtrip_constrs : MetaM Unit := diagnoseRoundTrip "constrs" ``golden_with_constrs

/-- Test: Round-trip for maximize problem. -/
def test_roundtrip_maximize : MetaM Unit := diagnoseRoundTrip "maximize" ``golden_maximize

/-- Test: Round-trip for complex problem. -/
def test_roundtrip_complex : MetaM Unit := diagnoseRoundTrip "complex" ``golden_complex

#eval test_roundtrip_simple
#eval test_roundtrip_two_vars
#eval test_roundtrip_constrs
#eval test_roundtrip_maximize
#eval test_roundtrip_complex

end RoundTripTests

/-! ## Structure Tests

Verify the internal structure of elaborated expressions. -/

section StructureTests

/-- Test: Minimization.mk has 4 arguments (domain, codomain, objFun, constraints). -/
def test_structure_args : MetaM Unit := do
  let e ← getConstExpr ``golden_simplest
  guard (e.getAppNumArgs == 4) <|>
    throwError "GOLDEN VIOLATION: Minimization.mk should have 4 arguments"

/-- Test: Codomain is ℝ for real-valued objectives. -/
def test_structure_codomain : MetaM Unit := do
  let e ← getConstExpr ``golden_simplest
  let minExpr ← MinimizationExpr.fromExpr e
  guard (← isDefEq minExpr.codomain (Lean.mkConst ``Real)) <|>
    throwError "GOLDEN VIOLATION: Codomain should be ℝ"

/-- Test: Constraints body is And for multiple constraints. -/
def test_structure_and_constraints : MetaM Unit := do
  let e ← getConstExpr ``golden_with_constrs
  let minExpr ← MinimizationExpr.fromExpr e
  let body := minExpr.constraints.bindingBody!
  guard (body.isAppOf ``And) <|>
    throwError "GOLDEN VIOLATION: Multiple constraints should be connected with And"

/-- GOLDEN: Single constraint problem for structure test. -/
def golden_single_constr := optimization (x : ℝ)
  minimize x
  subject to
    h : 0 ≤ x

/-- Test: Single constraint is not wrapped in And. -/
def test_structure_single_constraint : MetaM Unit := do
  let e ← getConstExpr ``golden_single_constr
  let minExpr ← MinimizationExpr.fromExpr e
  let body := minExpr.constraints.bindingBody!
  -- Single constraint should NOT be wrapped in And
  guard (!body.isAppOf ``And) <|>
    throwError "GOLDEN VIOLATION: Single constraint should not be wrapped in And"

#eval test_structure_args
#eval test_structure_codomain
#eval test_structure_and_constraints
#eval test_structure_single_constraint

end StructureTests

end CvxLean.Test.Syntax.Minimization
