import Mathlib.Data.Fin.Basic

/-!
Basic properties about `Fin`.
-/

namespace Fin

variable {n : ℕ}

instance [i : Fact (0 < n)] : OfNat (Fin n) 0 := ⟨⟨0, i.out⟩⟩

instance {n m x : ℕ} : OfNat (Fin n.succ ⊕ Fin m.succ) (x) where
  ofNat := if x <= n then Sum.inl ⟨x % n.succ, Nat.mod_lt x (Nat.succ_pos n)⟩
           else Sum.inr ⟨(x - n.succ) % m.succ, Nat.mod_lt _ (Nat.succ_pos m)⟩

end Fin
