namespace BEDC.Derived.Window6GaugeOrbit

/-
Theorem A no-go core: the first-seam clock residue, viewed as a function
of the free period-10 basepoint choice j in Z/10Z, is
seamResidue(j) = (7 - j) mod 10.  The finite certificate below shows that
this map runs through every clock residue.  Thus Window6/P_10 does not
forward-force a canonical residue; the physical-alpha residue 7 is one
basepoint-gauge choice among ten.  This file is the Lean companion to the
basepoint-free-gauge and alpha-external-gauge anchors, and does not claim a
physical-alpha derivation.
-/

def seamResidue (j : Nat) : Nat := (7 + 10 - j % 10) % 10

def seamResidueList : List Nat := (List.range 10).map seamResidue

def containsNat (needle : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => if x == needle then true else containsNat needle xs

def dedupNat : List Nat → List Nat
  | [] => []
  | x :: xs => if containsNat x xs then dedupNat xs else x :: dedupNat xs

def seamResidueDedup : List Nat := dedupNat seamResidueList

def allNatBelow (fuel : Nat) (p : Nat → Bool) : Bool :=
  match fuel with
  | 0 => true
  | n + 1 => allNatBelow n p && p n

def allListBelow (limit : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => (x < limit) && allListBelow limit xs

def coversZ10 : Bool := allNatBelow 10 (fun r => containsNat r seamResidueList)

def imageInsideZ10 : Bool := allListBelow 10 seamResidueList

example : seamResidue 0 = 7 := by decide

example : seamResidue 1 = 6 := by decide

example : seamResidue 7 = 0 := by decide

example : seamResidue 9 = 8 := by decide

example : seamResidueList = [7, 6, 5, 4, 3, 2, 1, 0, 9, 8] := by decide

theorem seamResidue_surjective_on_Z10 :
    seamResidueDedup.length = 10 ∧ coversZ10 = true := by
  exact ⟨rfl, rfl⟩

theorem seamResidue_bijective :
    seamResidueDedup.length = 10 ∧ coversZ10 = true ∧ imageInsideZ10 = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem residue_seven_unique_gauge :
    (seamResidueList.filter (· == 7)).length = 1 := by
  decide

end BEDC.Derived.Window6GaugeOrbit
