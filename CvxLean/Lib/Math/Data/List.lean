import Mathlib.Algebra.Ring.Basic

/-!
Some extra operations on lists.
-/

namespace List

variable {α}

def findIdx' (p : α → Prop) [DecidablePred p] : List α → Option ℕ
  | []     => none
  | (a::l) => if p a then some 0 else (findIdx' p l).map Nat.succ

def toVec (x : List α) : Fin x.length → α :=
  fun i => List.get x ⟨i, i.2⟩

def finRange' (d n : Nat) : List (Fin n) :=
  if _hn : 0 < n then (List.range d).map (fun i => ⟨i % n, Nat.mod_lt i (Nat.pos_of_ne_zero (Nat.ne_of_gt _hn))⟩) else []

def sum' [Zero α] [Add α] (L : List α) : α :=
  L.foldl (· + ·) 0

end List
