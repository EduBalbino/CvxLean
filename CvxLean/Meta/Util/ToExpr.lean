import Lean

/-!
Some `ToExpr` instances.
-/

section ToExpr

open Lean

instance : ToExpr Float where
  toExpr f :=
    match Json.Parser.num ⟨_, f.toString.startValidPos⟩ with
    | Std.Internal.Parsec.ParseResult.success _ res =>
        let e :=
          mkApp5
            (mkConst ``OfScientific.ofScientific [levelZero])
            (mkConst ``Float)
            (mkConst ``instOfScientificFloat)
            (toExpr res.mantissa.natAbs)
            (toExpr true)
            (toExpr res.exponent)
        if res.mantissa < 0 then
          mkApp (mkConst ``Float.neg) e
        else
          e
    | Std.Internal.Parsec.ParseResult.error _ _ =>
        mkApp (mkConst ``Float.ofNat) (toExpr (0 : Nat))
  toTypeExpr := mkConst ``Float

-- Note: ToExpr (Fin n) is provided by Lean's standard library.
-- A previous custom instance was incorrect (missing n and NeZero arguments to Fin.ofNat).

instance : ToExpr (Array Float) := by infer_instance

instance : ToExpr (Array (Array Float)) := by infer_instance

end ToExpr
