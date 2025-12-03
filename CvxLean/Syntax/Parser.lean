import Lean

/-!
This file defines how to parse variables, constraints, objective functions and full optimization
problems. Syntax matching these definitions is elaborated in `CvxLean/Syntax/Minimization.lean`.
-/

namespace CvxLean

open Lean Parser

declare_syntax_cat minimizationVar
syntax (ident <|> bracketedBinder) : minimizationVar

declare_syntax_cat letVar
syntax "with " Term.letDecl : letVar

declare_syntax_cat constraint
syntax (name := constraintIdent) Term.binderIdent " : " term : constraint

declare_syntax_cat minOrMax
syntax "minimize " : minOrMax
syntax "maximize " : minOrMax

scoped syntax (name := optimization)
  "optimization " minimizationVar* letVar*
    minOrMax term
    ("subject" "to" withPosition((colGe constraint)*))? : term

end CvxLean
