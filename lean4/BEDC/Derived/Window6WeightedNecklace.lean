import BEDC.Derived.Window6CyclicCount

set_option maxRecDepth 4096

namespace BEDC.Derived.Window6WeightedNecklace

open BEDC.Derived.Window6CyclicCount

/-
The period-ten golden clock has a basepoint-free C_10 orbit structure.
This file records the gauge-invariant weight grading of those orbits:
each orbit is represented by its least rotated word, and the Hamming weight
of that representative counts the shared number of marked clock positions.
The certificate is only about the finite golden-necklace orbit polynomial,
not about alpha.
-/

def addBitAt (acc j : Nat) : Nat :=
  acc + pow2 j

def rotateWord (m shift w : Nat) : Nat :=
  (List.range m).foldl
    (fun acc i => if bit w i then addBitAt acc ((i + shift) % m) else acc)
    0

def minNatList : List Nat → Nat
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

def orbitRepresentative (m w : Nat) : Nat :=
  minNatList ((List.range m).map (fun shift => rotateWord m shift w))

def canonicalOrbitWords (m : Nat) : List Nat :=
  (P m).filter (fun w => orbitRepresentative m w == w)

def weightOf (m w : Nat) : Nat :=
  (List.range m).foldl (fun acc i => if bit w i then acc + 1 else acc) 0

def countWeight (m target : Nat) : Nat :=
  (canonicalOrbitWords m).filter (fun w => weightOf m w == target) |>.length

def orbitWeightSpectrumFor (m maxWeight : Nat) : List Nat :=
  (List.range (maxWeight + 1)).map (fun target => countWeight m target)

def orbitWeightSpectrum : List Nat :=
  orbitWeightSpectrumFor 10 5

def orbitCountFromRepresentatives (m : Nat) : Nat :=
  (canonicalOrbitWords m).length

theorem orbitRepresentative_count_p10 :
    orbitCountFromRepresentatives 10 = 15 := by
  decide

theorem weightedNecklace_p10 :
    orbitWeightSpectrum = [1, 1, 4, 5, 3, 1] := by
  decide

theorem weightSpectrum_sum_eq_orbitCount :
    orbitWeightSpectrum.foldl (· + ·) 0 = 15 := by
  decide

theorem weightSpectrum_sum_eq_representative_count :
    orbitWeightSpectrum.foldl (· + ·) 0 = orbitCountFromRepresentatives 10 := by
  decide

end BEDC.Derived.Window6WeightedNecklace
