import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.PhiDivisorSum

namespace BEDC.Derived.TotientSummatoryUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.PhiDivisorSum
open BEDC.Derived.PrimeUp

abbrev NatZero : BHist := BHist.Empty
abbrev NatOne : BHist := BEDC.Derived.PadicUp.NatOne
abbrev NatTwo : BHist := BHist.e1 NatOne
abbrev NatThree : BHist := BHist.e1 NatTwo
abbrev NatFour : BHist := BHist.e1 NatThree

def phiRowsNat : List (List BHist) -> Nat
  | [] => 0
  | row :: rows => eulerPhiFactorsNat row + phiRowsNat rows

def totientSummatoryNat (rows : List (List BHist)) : Nat :=
  phiRowsNat rows

def totientSummatory (rows : List (List BHist)) : BHist :=
  natToUnary (totientSummatoryNat rows)

def phiRowsIntegerTerms (rows : List (List BHist)) : List BEDC.Algebra.Rel.IntegerUp :=
  rows.map
    (fun row =>
      BEDC.Derived.RationalUp.intOfNat
        (eulerPhiFactors row) (eulerPhiFactors_unary row))

def totientSummatoryInteger (rows : List (List BHist)) : BEDC.Algebra.Rel.IntegerUp :=
  listSum IntegerUp_RelCommRing (phiRowsIntegerTerms rows)

inductive FactorRowsValues : List (List BHist) -> List BHist -> Prop where
  | nil : FactorRowsValues [] []
  | cons {row : List BHist} {n : BHist}
      {rows : List (List BHist)} {values : List BHist} :
      PrimeFactorization n row ->
        FactorRowsValues rows values ->
          FactorRowsValues (row :: rows) (n :: values)

inductive UnaryInitialSegment : BHist -> List BHist -> Prop where
  | one : UnaryInitialSegment NatOne [NatOne]
  | succ {n : BHist} {values : List BHist} :
      UnaryInitialSegment n values ->
        UnaryInitialSegment (BHist.e1 n) (values ++ [BHist.e1 n])

theorem factorRowsValues_value_unary
    {rows : List (List BHist)} {values : List BHist} {n : BHist} :
    FactorRowsValues rows values ->
      n ∈ values -> UnaryHistory n := by
  intro factorized member
  induction factorized with
  | nil =>
      cases member
  | cons head tail ih =>
      cases member with
      | head =>
          exact head.left
      | tail _ tailMember =>
          exact ih tailMember

structure TotientFactorPrefix where
  rows : List (List BHist)
  values : List BHist
  value_factorized : FactorRowsValues rows values

structure TotientSummatoryPrefix (n sum : BHist) where
  rows : List (List BHist)
  values : List BHist
  values_initial : UnaryInitialSegment n values
  value_factorized : FactorRowsValues rows values
  sum_hsame : hsame (totientSummatory rows) sum

def TotientFactorPrefix.phiSumNat (pack : TotientFactorPrefix) : Nat :=
  totientSummatoryNat pack.rows

def TotientFactorPrefix.phiSum (pack : TotientFactorPrefix) : BHist :=
  totientSummatory pack.rows

theorem unaryInitialSegment_endpoint_unary
    {n : BHist} {values : List BHist} :
    UnaryInitialSegment n values -> UnaryHistory n := by
  intro initial
  induction initial with
  | one =>
      exact unary_e1_closed unary_empty
  | succ _ ih =>
      exact unary_e1_closed ih

theorem phiRowsNat_nil :
    phiRowsNat [] = 0 := by
  rfl

theorem phiRowsNat_cons (row : List BHist) (rows : List (List BHist)) :
    phiRowsNat (row :: rows) =
      eulerPhiFactorsNat row + phiRowsNat rows := by
  rfl

theorem totientSummatoryNat_nil :
    totientSummatoryNat [] = 0 := by
  rfl

theorem totientSummatoryNat_cons (row : List BHist) (rows : List (List BHist)) :
    totientSummatoryNat (row :: rows) =
      eulerPhiFactorsNat row + totientSummatoryNat rows := by
  rfl

theorem totientSummatory_unary (rows : List (List BHist)) :
    UnaryHistory (totientSummatory rows) := by
  unfold totientSummatory
  exact natToUnary_unary _

theorem totientFactorPrefix_value_unary
    {pack : TotientFactorPrefix} {n : BHist} :
    n ∈ pack.values -> UnaryHistory n := by
  intro member
  exact factorRowsValues_value_unary pack.value_factorized member

theorem totientFactorPrefix_phiSum_unary (pack : TotientFactorPrefix) :
    UnaryHistory pack.phiSum :=
  totientSummatory_unary pack.rows

theorem totientSummatoryInteger_nil :
    IntEq (totientSummatoryInteger []) intZero := by
  exact BEDC.Derived.RationalUp.IntEq_refl intZero

theorem totientSummatoryInteger_cons
    (row : List BHist) (rows : List (List BHist)) :
    IntEq (totientSummatoryInteger (row :: rows))
      (IntAdd
        (BEDC.Derived.RationalUp.intOfNat
          (eulerPhiFactors row) (eulerPhiFactors_unary row))
        (totientSummatoryInteger rows)) := by
  exact BEDC.Derived.RationalUp.IntEq_refl (totientSummatoryInteger (row :: rows))

theorem gauss_phi_divisor_sum_export
    {n : BHist} {profile : PrimePowerProfile} :
    DivisorCountOfProfile n (divisorCountProfile profile) profile ->
      hsame (profilePhiDivisorSum profile) n :=
  gauss_phi_divisor_sum_of_prime_factorization

theorem gauss_phi_divisor_sum_nat_export
    {profile : PrimePowerProfile} :
    ProfileValid profile ->
      profilePhiDivisorSumNat profile = profileProductNat profile :=
  gauss_phi_divisor_sum_nat_of_profile

theorem totientSummatoryNat_zero :
    totientSummatoryNat [] = 0 := by
  rfl

theorem totientSummatory_zero :
    hsame (totientSummatory []) NatZero := by
  exact hsame_refl NatZero

theorem totientSummatoryNat_one :
    totientSummatoryNat [[]] = 1 := by
  rfl

theorem totientSummatory_one :
    hsame (totientSummatory [[]]) NatOne := by
  exact hsame_refl NatOne

theorem totientSummatoryNat_two :
    totientSummatoryNat [[], [NatTwo]] = 2 := by
  rfl

theorem totientSummatory_two :
    hsame (totientSummatory [[], [NatTwo]]) NatTwo := by
  exact hsame_refl NatTwo

theorem totientSummatoryNat_three :
    totientSummatoryNat [[], [NatTwo], [NatThree]] = 4 := by
  rfl

theorem totientSummatory_three :
    hsame (totientSummatory [[], [NatTwo], [NatThree]]) NatFour := by
  exact hsame_refl NatFour

theorem natTwo_prime : NatPrime NatTwo := by
  exact NatPrime_first_pair.left

theorem natThree_prime : NatPrime NatThree := by
  exact NatPrime_first_pair.right

theorem primeFactorizationProduct_one :
    PrimeFactorizationProduct [] NatOne := by
  rfl

theorem primeFactorizationProduct_two :
    PrimeFactorizationProduct [NatTwo] NatTwo := by
  exact And.intro natTwo_prime
    (Exists.intro NatOne
      (And.intro primeFactorizationProduct_one
        BEDC.Derived.PrimeUp.NatMul_first_prime_unit_result))

theorem primeFactorizationProduct_three :
    PrimeFactorizationProduct [NatThree] NatThree := by
  exact And.intro natThree_prime
    (Exists.intro NatOne
      (And.intro primeFactorizationProduct_one
        (BEDC.Derived.PrimeUp.NatMul.succ
          (BEDC.Derived.PrimeUp.NatMul.zero natThree_prime.left)
          (BEDC.FKernel.Cont.cont_left_unit NatThree))))

theorem primeFactorization_one :
    PrimeFactorization NatOne [] := by
  exact And.intro (unary_e1_closed unary_empty) primeFactorizationProduct_one

theorem primeFactorization_two :
    PrimeFactorization NatTwo [NatTwo] := by
  exact And.intro natTwo_prime.left primeFactorizationProduct_two

theorem primeFactorization_three :
    PrimeFactorization NatThree [NatThree] := by
  exact And.intro natThree_prime.left primeFactorizationProduct_three

def totientPrefixThree : TotientFactorPrefix where
  rows := [[], [NatTwo], [NatThree]]
  values := [NatOne, NatTwo, NatThree]
  value_factorized :=
    FactorRowsValues.cons primeFactorization_one
      (FactorRowsValues.cons primeFactorization_two
        (FactorRowsValues.cons primeFactorization_three FactorRowsValues.nil))

theorem totientPrefixThree_sum :
    hsame totientPrefixThree.phiSum NatFour := by
  exact hsame_refl NatFour

theorem unaryInitialSegment_three :
    UnaryInitialSegment NatThree [NatOne, NatTwo, NatThree] := by
  exact UnaryInitialSegment.succ
    (UnaryInitialSegment.succ UnaryInitialSegment.one)

def totientSummatoryPrefixThree :
    TotientSummatoryPrefix NatThree NatFour where
  rows := [[], [NatTwo], [NatThree]]
  values := [NatOne, NatTwo, NatThree]
  values_initial := unaryInitialSegment_three
  value_factorized := totientPrefixThree.value_factorized
  sum_hsame := hsame_refl NatFour

end BEDC.Derived.TotientSummatoryUp
