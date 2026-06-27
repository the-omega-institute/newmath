import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.PrimeUp.PrimeShape
import BEDC.Derived.PrimeUp.UniqueFactorization

set_option maxRecDepth 3000

namespace BEDC.Derived.PrimeSieveOddExactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

private abbrev NatOne : BHist := BHist.e1 BHist.Empty

def OddCandidate (n : Nat) : Prop :=
  3 ≤ n ∧ n % 2 = 1

instance (n : Nat) : Decidable (OddCandidate n) := by
  unfold OddCandidate
  infer_instance

def rejectsBy (p n : Nat) : Bool :=
  decide (p < n ∧ n % p = 0)

def oddCandidatesUpTo (limit : Nat) : List Nat :=
  (List.range (limit + 1)).filter (fun n => decide (OddCandidate n))

def sieveBy (p : Nat) (xs : List Nat) : List Nat :=
  xs.filter (fun n => !(rejectsBy p n))

def oddSieveByPivots : List Nat -> List Nat -> List Nat
  | [], survivors => survivors
  | p :: ps, survivors => oddSieveByPivots ps (sieveBy p survivors)

def oddSieveFromCandidates (xs : List Nat) : List Nat :=
  oddSieveByPivots xs xs

def oddPrimeSieve (limit : Nat) : List Nat :=
  oddSieveFromCandidates (oddCandidatesUpTo limit)

def oddSieveSurvives (limit n : Nat) : Prop :=
  n ∈ oddPrimeSieve limit

def natEqBool : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natEqBool a b

def inListNat (n : Nat) : List Nat -> Bool
  | [] => false
  | x :: xs =>
      match natEqBool n x with
      | true => true
      | false => inListNat n xs

def oddSieveSurvivesBool (limit n : Nat) : Bool :=
  inListNat n (oddPrimeSieve limit)

def primeWindowSixteenBool (n : Nat) : Bool :=
  inListNat n [3, 5, 7, 11, 13]

theorem oddCandidate_three : OddCandidate 3 := by
  unfold OddCandidate
  exact ⟨Nat.le_refl 3, rfl⟩

theorem oddCandidate_not_even {n : Nat} :
    OddCandidate n -> n % 2 = 0 -> False := by
  intro candidate even
  rw [candidate.right] at even
  cases even

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOne tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem natOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix NatOne (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix NatOne (BHist.e1 (natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (natToUnary (Nat.succ n))
    (natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

theorem NatThree_prime : NatPrime (natToUnary 3) := by
  have large : NatUnaryStrictPrefix NatOne (natToUnary 3) :=
    natOne_strict_natToUnary_succ_succ 1
  change NatPrime (minFactor (natToUnary 3) large)
  exact minFactor_prime large

theorem NatFive_prime : NatPrime (natToUnary 5) := by
  have large : NatUnaryStrictPrefix NatOne (natToUnary 5) :=
    natOne_strict_natToUnary_succ_succ 3
  change NatPrime (minFactor (natToUnary 5) large)
  exact minFactor_prime large

theorem NatSeven_prime : NatPrime (natToUnary 7) := by
  have large : NatUnaryStrictPrefix NatOne (natToUnary 7) :=
    natOne_strict_natToUnary_succ_succ 5
  change NatPrime (minFactor (natToUnary 7) large)
  exact minFactor_prime large

theorem NatEleven_prime : NatPrime (natToUnary 11) := by
  have large : NatUnaryStrictPrefix NatOne (natToUnary 11) :=
    natOne_strict_natToUnary_succ_succ 9
  change NatPrime (minFactor (natToUnary 11) large)
  exact minFactor_prime large

theorem NatThirteen_prime : NatPrime (natToUnary 13) := by
  have large : NatUnaryStrictPrefix NatOne (natToUnary 13) :=
    natOne_strict_natToUnary_succ_succ 11
  change NatPrime (minFactor (natToUnary 13) large)
  exact minFactor_prime large

theorem oddPrimeSieve_sixteen_exact :
    oddPrimeSieve 16 = [3, 5, 7, 11, 13] := by
  decide

theorem oddSieveSurvivesBool_sixteen_exact (n : Nat) :
    oddSieveSurvivesBool 16 n = primeWindowSixteenBool n := by
  unfold oddSieveSurvivesBool primeWindowSixteenBool
  exact congrArg (inListNat n) oddPrimeSieve_sixteen_exact

theorem oddSieveSurvivesBool_sixteen_iff_window {n : Nat} :
    oddSieveSurvivesBool 16 n = true ↔ primeWindowSixteenBool n = true := by
  constructor
  · intro survives
    exact (oddSieveSurvivesBool_sixteen_exact n).symm.trans survives
  · intro listed
    exact (oddSieveSurvivesBool_sixteen_exact n).trans listed

theorem smallRangeOddSieveExactness :
    (oddSieveSurvivesBool 16 3 = true ∧ NatPrime (natToUnary 3)) ∧
      (oddSieveSurvivesBool 16 5 = true ∧ NatPrime (natToUnary 5)) ∧
        (oddSieveSurvivesBool 16 7 = true ∧ NatPrime (natToUnary 7)) ∧
          (oddSieveSurvivesBool 16 11 = true ∧ NatPrime (natToUnary 11)) ∧
            (oddSieveSurvivesBool 16 13 = true ∧ NatPrime (natToUnary 13)) ∧
              oddSieveSurvivesBool 16 9 = false ∧
                oddSieveSurvivesBool 16 15 = false := by
  exact
    ⟨⟨by decide, NatThree_prime⟩,
      ⟨⟨by decide, NatFive_prime⟩,
        ⟨⟨by decide, NatSeven_prime⟩,
          ⟨⟨by decide, NatEleven_prime⟩,
            ⟨⟨by decide, NatThirteen_prime⟩,
              ⟨by decide, by decide⟩⟩⟩⟩⟩⟩

end BEDC.Derived.PrimeSieveOddExactnessUp
