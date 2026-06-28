import BEDC.Derived.AbundantDeficientUp
import BEDC.Derived.PracticalNumberUp

namespace BEDC.Derived.WeirdNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_length)
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.AbundantDeficientUp
open BEDC.Derived.PracticalNumberUp

def listNatSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + listNatSum xs

def subsetSumsNat (xs : List Nat) : List Nat :=
  PracticalNumberUp.subsetSumsNat xs

def boundedSubsetSumsNat (target : Nat) : List Nat -> List Nat
  | [] => [0]
  | x :: xs =>
      let tail := boundedSubsetSumsNat target xs
      tail ++ (tail.map (fun s => x + s)).filter (fun s => s ≤ target)

def listHasNat (target : Nat) (xs : List Nat) : Bool :=
  PracticalNumberUp.listContainsNat target xs

def divisorsNatByScan (n : Nat) : List Nat :=
  PracticalNumberUp.divisorsNat n

def properDivisorsNatByScan (n : Nat) : List Nat :=
  PracticalNumberUp.properDivisorsNat n

def sigmaNatByDivisorScan (n : Nat) : Nat :=
  listNatSum (divisorsNatByScan n)

def properDivisorSubsetSumHits (n : Nat) : Bool :=
  listHasNat n (boundedSubsetSumsNat n (properDivisorsNatByScan n))

def NatAbundantBySigma (n : Nat) : Prop :=
  2 * n < sigmaNatByDivisorScan n

def NatSemiperfect (n : Nat) : Prop :=
  properDivisorSubsetSumHits n = true

def NatWeird (n : Nat) : Prop :=
  NatAbundantBySigma n ∧ (NatSemiperfect n -> False)

def natAbundantBySigmaBool (n : Nat) : Bool :=
  decide (2 * n < sigmaNatByDivisorScan n)

def AbundantBySigmaNumber (n : BHist) : Prop :=
  NatAbundantBySigma (bwordLength n)

def SemiperfectNumber (n : BHist) : Prop :=
  NatSemiperfect (bwordLength n)

def WeirdNumber (n : BHist) : Prop :=
  AbundantBySigmaNumber n ∧ (SemiperfectNumber n -> False)

def weirdNatBool (n : Nat) : Bool :=
  natAbundantBySigmaBool n && !properDivisorSubsetSumHits n

def weirdNumbersBelow (limit : Nat) : List Nat :=
  (List.range limit).filter weirdNatBool

def NatSeventy : BHist :=
  natToUnary 70

def profileSeventy : PrimePowerProfile :=
  [{ prime := natToUnary 2, exponent := 1 },
    { prime := natToUnary 5, exponent := 1 },
    { prime := natToUnary 7, exponent := 1 }]

theorem NatSeventy_length :
    bwordLength NatSeventy = 70 := by
  unfold NatSeventy
  exact natToUnary_length 70

theorem properDivisorsSeventy_value :
    properDivisorsNatByScan 70 = [1, 2, 5, 7, 10, 14, 35] := by
  rfl

theorem properDivisorsSeventy_nodup_count :
    List.Nodup (properDivisorsNatByScan 70) ∧
      List.count 1 (properDivisorsNatByScan 70) = 1 ∧
      List.count 2 (properDivisorsNatByScan 70) = 1 ∧
      List.count 5 (properDivisorsNatByScan 70) = 1 ∧
      List.count 7 (properDivisorsNatByScan 70) = 1 ∧
      List.count 10 (properDivisorsNatByScan 70) = 1 ∧
      List.count 14 (properDivisorsNatByScan 70) = 1 ∧
      List.count 35 (properDivisorsNatByScan 70) = 1 := by
  decide

theorem divisorsSeventy_value :
    divisorsNatByScan 70 = [1, 2, 5, 7, 10, 14, 35, 70] := by
  rfl

theorem sigmaSeventy_scan_value :
    sigmaNatByDivisorScan 70 = 144 := by
  rfl

theorem profileSeventy_sigma_value :
    sigmaNat profileSeventy = 144 := by
  rfl

theorem profileSeventy_value :
    profileValueNat profileSeventy = 70 := by
  rfl

theorem seventy_profile_abundant :
    IsAbundantProfile profileSeventy := by
  unfold IsAbundantProfile
  rw [profileSeventy_sigma_value, profileSeventy_value]
  decide

theorem seventy_abundant_by_sigma_scan :
    NatAbundantBySigma 70 := by
  unfold NatAbundantBySigma
  rw [sigmaSeventy_scan_value]
  decide

theorem seventy_not_semiperfect_by_subset_scan :
    NatSemiperfect 70 -> False := by
  unfold NatSemiperfect properDivisorSubsetSumHits properDivisorsNatByScan
  decide

theorem seventy_nat_weird :
    NatWeird 70 := by
  exact ⟨seventy_abundant_by_sigma_scan, seventy_not_semiperfect_by_subset_scan⟩

theorem seventy_weird_number :
    WeirdNumber NatSeventy := by
  unfold WeirdNumber AbundantBySigmaNumber SemiperfectNumber
  rw [NatSeventy_length]
  exact seventy_nat_weird

theorem no_weird_nat_below_seventy_by_bounded_scan :
    weirdNumbersBelow 70 = [] := by
  decide

theorem seventy_first_weird_by_bounded_scan :
    weirdNumbersBelow 71 = [70] := by
  decide

theorem seventy_minimal_weird_by_bounded_scan :
    weirdNumbersBelow 70 = [] ∧ weirdNumbersBelow 71 = [70] := by
  constructor
  · exact no_weird_nat_below_seventy_by_bounded_scan
  · exact seventy_first_weird_by_bounded_scan

end BEDC.Derived.WeirdNumberUp
