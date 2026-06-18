import BEDC.Derived.Window6CyclicCount

set_option maxRecDepth 4096

namespace BEDC.Derived.Window6NecklaceOrbitCount

abbrev pow2 : Nat -> Nat :=
  BEDC.Derived.Window6CyclicCount.pow2

abbrev bit : Nat -> Nat -> Bool :=
  BEDC.Derived.Window6CyclicCount.bit

abbrev P : Nat -> List Nat :=
  BEDC.Derived.Window6CyclicCount.P

abbrev cyclicCount : Nat -> Nat :=
  BEDC.Derived.Window6CyclicCount.cyclicCount

/--
The period-ten Window6 clock has a basepoint gauge: rotating the ten bit
positions changes the written word while preserving the cyclic no-adjacent-one
condition.  The finite certificate below counts the quotient by the `C_10`
rotation action.  It is a basepoint-independent combinatorial count, and it
does not assert a physical-alpha derivation.
-/

def rotBit (k w i : Nat) : Bool :=
  bit w ((i + 10 - k % 10) % 10)

def rot (k w : Nat) : Nat :=
  (List.range 10).foldl
    (fun acc i => if rotBit k w i then acc + pow2 i else acc) 0

def minNatList : List Nat -> Nat
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

def rotations (w : Nat) : List Nat :=
  (List.range 10).map (fun k => rot k w)

def orbitRepresentative (w : Nat) : Nat :=
  minNatList (rotations w)

def containsNat (needle : Nat) : List Nat -> Bool
  | [] => false
  | x :: xs => if x == needle then true else containsNat needle xs

def dedupNat : List Nat -> List Nat
  | [] => []
  | x :: xs => if containsNat x xs then dedupNat xs else x :: dedupNat xs

def orbitRepresentatives : List Nat :=
  dedupNat ((P 10).map orbitRepresentative)

def orbitCount : Nat :=
  orbitRepresentatives.length

def fixedBy (k w : Nat) : Bool :=
  rot k w == w

def fixCount (k : Nat) : Nat :=
  ((P 10).filter (fun w => fixedBy k w)).length

def fixCountTable : List Nat :=
  (List.range 10).map fixCount

def burnsideFixSum : Nat :=
  fixCountTable.foldl (fun acc n => acc + n) 0

def burnsideOrbitCount : Nat :=
  burnsideFixSum / 10

theorem p10_card : cyclicCount 10 = 123 :=
  BEDC.Derived.Window6CyclicCount.cyclicCount_ten

theorem fixCountTable_eq :
    fixCountTable = [123, 1, 3, 1, 3, 11, 3, 1, 3, 1] := by
  rfl

theorem burnside_fix_sum : burnsideFixSum = 150 := by
  rfl

theorem burnside_orbit_count : burnsideOrbitCount = 15 := by
  rfl

theorem orbitCount_p10 : orbitCount = 15 := by
  rfl

end BEDC.Derived.Window6NecklaceOrbitCount
