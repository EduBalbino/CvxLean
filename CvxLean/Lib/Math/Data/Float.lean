import Mathlib.Data.Matrix.Basic

/-! ## Typed Matrix Infrastructure

We use `Matrix (Fin n) (Fin m) Float` for type-safe dimension checking.
Conversion functions bridge to runtime `Array` for the CvxLean solver.
-/

/-- Runtime matrix type for solver interface -/
abbrev Mat := Array (Array Float)

/-- Runtime vector type -/
abbrev Vec := Array Float

/-- Convert typed matrix to runtime array -/
def matToArray {n m : Nat} (M : Matrix (Fin n) (Fin m) Float) : Mat :=
  Array.ofFn fun i => Array.ofFn fun j => M i j

/-- Convert runtime array to typed matrix (with bounds checking) -/
def matOfArray {n m : Nat} (arr : Mat) : Matrix (Fin n) (Fin m) Float :=
  fun i j => (arr.getD i.val #[]).getD j.val 0.0

namespace Mat

def zeros (rows cols : Nat) : Mat := Id.run do
  let mut result : Mat := #[]
  for _ in [:rows] do
    let mut row : Array Float := #[]
    for _ in [:cols] do row := row.push 0.0
    result := result.push row
  result

def eye (dim : Nat) : Mat := Id.run do
  let mut result := zeros dim dim
  for i in [:dim] do
    result := result.modify i (·.set! i 1.0)
  result

def ones (rows cols : Nat) : Mat := Id.run do
  let mut result : Mat := #[]
  for _ in [:rows] do
    let mut row : Array Float := #[]
    for _ in [:cols] do row := row.push 1.0
    result := result.push row
  result

@[inline] def rows (M : Mat) : Nat := M.size

@[inline] def cols (M : Mat) : Nat := (M.getD 0 #[]).size

@[inline] def get (M : Mat) (i j : Nat) : Float :=
  (M.getD i #[]).getD j 0.0

def set (M : Mat) (i j : Nat) (v : Float) : Mat :=
  M.modify i (·.set! j v)

def add (A B : Mat) : Mat := Id.run do
  let mut result : Mat := #[]
  for i in [:A.size] do
    let mut row : Array Float := #[]
    for j in [:(A.getD i #[]).size] do
      row := row.push (A.get i j + B.get i j)
    result := result.push row
  result

def sub (A B : Mat) : Mat := Id.run do
  let mut result : Mat := #[]
  for i in [:A.size] do
    let mut row : Array Float := #[]
    for j in [:(A.getD i #[]).size] do
      row := row.push (A.get i j - B.get i j)
    result := result.push row
  result

def smul (c : Float) (M : Mat) : Mat :=
  M.map (·.map (c * ·))

def neg (M : Mat) : Mat := smul (-1.0) M

def mul (A B : Mat) : Mat := Id.run do
  let aRows := A.rows
  let bCols := B.cols
  let aCols := A.cols
  let mut result := zeros aRows bCols
  for i in [:aRows] do
    for j in [:bCols] do
      let mut sum := 0.0
      for k in [:aCols] do
        sum := sum + A.get i k * B.get k j
      result := result.set i j sum
  result

def transpose (M : Mat) : Mat := Id.run do
  let r := M.rows
  let c := M.cols
  let mut result := zeros c r
  for i in [:r] do
    for j in [:c] do
      result := result.set j i (M.get i j)
  result

def vstack (A B : Mat) : Mat := A ++ B

def hstack (A B : Mat) : Mat := Id.run do
  let mut result : Mat := #[]
  for i in [:A.size] do
    result := result.push ((A.getD i #[]) ++ (B.getD i #[]))
  result

/-- Compute 2×2 matrix inverse -/
def inv2x2 (M : Mat) : Option Mat :=
  let a := M.get 0 0; let b := M.get 0 1
  let c := M.get 1 0; let d := M.get 1 1
  let det := a * d - b * c
  if det.abs < 1e-20 then none  -- Very loose threshold for debugging
  else some #[#[d / det, -b / det], #[-c / det, a / det]]

/-- Compute 3×3 matrix inverse using cofactor expansion -/
def inv3x3 (M : Mat) : Option Mat := Id.run do
  let a := M.get 0 0; let b := M.get 0 1; let c := M.get 0 2
  let d := M.get 1 0; let e := M.get 1 1; let f := M.get 1 2
  let g := M.get 2 0; let h := M.get 2 1; let i := M.get 2 2

  let det := a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)
  if det.abs < 1e-12 then return none

  let invDet := 1.0 / det
  some #[
    #[(e*i - f*h) * invDet, (c*h - b*i) * invDet, (b*f - c*e) * invDet],
    #[(f*g - d*i) * invDet, (a*i - c*g) * invDet, (c*d - a*f) * invDet],
    #[(d*h - e*g) * invDet, (b*g - a*h) * invDet, (a*e - b*d) * invDet]
  ]

def inv (M : Mat) : Option Mat :=
  if M.rows == 2 && M.cols == 2 then inv2x2 M
  else if M.rows == 3 && M.cols == 3 then inv3x3 M
  else none

/-- Element-wise multiplication (Hadamard product) -/
def hadamard (A B : Mat) : Mat := Id.run do
  let mut result : Mat := #[]
  for i in [:A.size] do
    let mut row : Array Float := #[]
    for j in [:(A.getD i #[]).size] do
      row := row.push (A.get i j * B.get i j)
    result := result.push row
  result

def toString (M : Mat) (name : String := "") : String := Id.run do
  let mut s := if name.isEmpty then "" else s!"{name} = \n"
  for i in [:M.rows] do
    s := s ++ "  ["
    for j in [:M.cols] do
      let v := M.get i j
      s := s ++ s!"{if v >= 0 then " " else ""}{v}"
      if j + 1 < M.cols then s := s ++ ", "
    s := s ++ "]\n"
  s

end Mat
