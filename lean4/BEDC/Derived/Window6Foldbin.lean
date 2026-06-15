namespace BEDC.Derived.Window6Foldbin

/--
Foldbin tail-cube four-cell partition for the Window6 forced-window
structure.  The finite certificate below computes the four micro-cells with
sizes 27, 22, 9, and 6, and checks that they are pairwise disjoint and cover
the vertices 0 through 63 inside the mathlib-free Lean kernel.
-/

def pow2 : Nat -> Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

def bit (w i : Nat) : Bool :=
  (w / pow2 i) % 2 == 1

def bitWeight (b : Bool) (n : Nat) : Nat :=
  if b then n else 0

def fibWeight : Nat -> Nat
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 5
  | 4 => 8
  | 5 => 13
  | _ => 0

def fibWeights : List Nat :=
  [1, 2, 3, 5, 8, 13]

def v6 (w : Nat) : Nat :=
  (List.range 6).foldl
    (fun acc i => acc + bitWeight (bit w i) (fibWeight i)) 0

def weight (w : Nat) : Nat :=
  (List.range 6).foldl
    (fun acc i => acc + bitWeight (bit w i) 1) 0

def noAdjacent6 (w : Nat) : Bool :=
  !(bit w 0 && bit w 1) &&
  !(bit w 1 && bit w 2) &&
  !(bit w 2 && bit w 3) &&
  !(bit w 3 && bit w 4) &&
  !(bit w 4 && bit w 5)

def isX6 (w : Nat) : Bool :=
  decide (w < 64) && noAdjacent6 w

def isBoundary (w : Nat) : Bool :=
  isX6 w && bit w 0 && bit w 5

def isCyclic (w : Nat) : Bool :=
  isX6 w && !isBoundary w

def X6 : List Nat :=
  (List.range 64).filter isX6

def boundary : List Nat :=
  X6.filter isBoundary

def cyclic : List Nat :=
  X6.filter isCyclic

def inBlock (i w : Nat) : Bool :=
  match i with
  | 0 => isCyclic w && (weight w == 2)
  | 1 => isCyclic w && (weight w == 1)
  | 2 => isCyclic w && ((weight w == 0) || (weight w == 3))
  | 3 => isBoundary w
  | _ => false

def block (i : Nat) : List Nat :=
  X6.filter (fun w => inBlock i w)

def tailBit (t j : Nat) : Bool :=
  bit t j

def foldbinTailOK (w t : Nat) : Bool :=
  !(tailBit t 0 && tailBit t 1) &&
  !(tailBit t 1 && tailBit t 2) &&
  !(bit w 5 && tailBit t 0)

def foldbinValue (w t : Nat) : Nat :=
  v6 w +
  bitWeight (tailBit t 0) 21 +
  bitWeight (tailBit t 1) 34 +
  bitWeight (tailBit t 2) 55

def foldbinFiber (w : Nat) : List Nat :=
  ((List.range 8).filter
    (fun t => foldbinTailOK w t && decide (foldbinValue w t <= 63))).map
      (fun t => foldbinValue w t)

def listHas (v : Nat) : List Nat -> Bool
  | [] => false
  | x :: xs => (x == v) || listHas v xs

def inFoldbinFiber (w v : Nat) : Bool :=
  listHas v (foldbinFiber w)

def inMicroCell (i v : Nat) : Bool :=
  (block i).any (fun w => inFoldbinFiber w v)

def microCell (i : Nat) : List Nat :=
  (List.range 64).filter (fun v => inMicroCell i v)

def cellIntersection (i j : Nat) : List Nat :=
  (microCell i).filter (fun v => listHas v (microCell j))

def microCellsUnion : List Nat :=
  (List.range 64).filter
    (fun v =>
      listHas v (microCell 0) ||
      listHas v (microCell 1) ||
      listHas v (microCell 2) ||
      listHas v (microCell 3))

theorem X6_card : X6.length = 21 := by
  rfl

theorem block_cards :
    (block 0).length = 9 ∧
    (block 1).length = 6 ∧
    (block 2).length = 3 ∧
    (block 3).length = 3 := by
  decide

theorem microCell_sizes :
    (microCell 0).length = 27 ∧
    (microCell 1).length = 22 ∧
    (microCell 2).length = 9 ∧
    (microCell 3).length = 6 := by
  decide

theorem microCell_zero_card : (microCell 0).length = 27 := by
  rfl

theorem microCell_one_card : (microCell 1).length = 22 := by
  rfl

theorem microCell_two_card : (microCell 2).length = 9 := by
  rfl

theorem microCell_three_card : (microCell 3).length = 6 := by
  rfl

theorem microCells_disjoint :
    cellIntersection 0 1 = [] ∧
    cellIntersection 0 2 = [] ∧
    cellIntersection 0 3 = [] ∧
    cellIntersection 1 2 = [] ∧
    cellIntersection 1 3 = [] ∧
    cellIntersection 2 3 = [] := by
  decide

theorem microCells_cover : microCellsUnion = List.range 64 := by
  decide

theorem microCells_partition :
    (microCell 0).length = 27 ∧
    (microCell 1).length = 22 ∧
    (microCell 2).length = 9 ∧
    (microCell 3).length = 6 ∧
    cellIntersection 0 1 = [] ∧
    cellIntersection 0 2 = [] ∧
    cellIntersection 0 3 = [] ∧
    cellIntersection 1 2 = [] ∧
    cellIntersection 1 3 = [] ∧
    cellIntersection 2 3 = [] ∧
    microCellsUnion = List.range 64 := by
  decide

end BEDC.Derived.Window6Foldbin
