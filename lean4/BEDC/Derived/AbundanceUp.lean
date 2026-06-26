import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.IntUp.CommRing
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.AbundanceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ArithmeticFnUp

def ProperDivisorSumNat (entries : List BHist) : Nat :=
  sigmaFactorsNat entries - bwordLength (factorListProductFn entries)

def ProperDivisorSumOfFactorization (n : BHist) (s : Nat) : Prop :=
  ∃ entries : List BHist,
    BEDC.Derived.PrimeUp.PrimeFactorization n entries ∧
      s = ProperDivisorSumNat entries

def IsAbundant (entries : List BHist) : Prop :=
  2 * bwordLength (factorListProductFn entries) < sigmaFactorsNat entries

def IsDeficient (entries : List BHist) : Prop :=
  sigmaFactorsNat entries < 2 * bwordLength (factorListProductFn entries)

def IsPerfect (entries : List BHist) : Prop :=
  sigmaFactorsNat entries = 2 * bwordLength (factorListProductFn entries)

def FactorizationNumberClass (entries : List BHist) : Prop :=
  IsAbundant entries ∨ IsDeficient entries ∨ IsPerfect entries

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        unary_hsame_of_length resultData.left (natToUnary_unary _)
          ((NatMul_bwordLength resultData.right).trans (by
            rw [natToUnary_length, natToUnary_length, natToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

private theorem natAddLeToLeSub (a c b : Nat) :
    a + c ≤ b -> c ≤ b - a := by
  induction a generalizing b with
  | zero =>
      intro h
      rw [Nat.zero_add] at h
      rw [Nat.sub_zero]
      exact h
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          rw [Nat.succ_add] at h
          exact False.elim (Nat.not_succ_le_zero _ h)
      | succ b =>
          intro h
          have lowered : a + c ≤ b := by
            rw [Nat.succ_add] at h
            exact Nat.succ_le_succ_iff.mp h
          have recResult : c ≤ b - a := ih b lowered
          rw [Nat.succ_sub_succ]
          exact recResult

private theorem natPosLeSubToAddLe (a c b : Nat) :
    0 < c -> c ≤ b - a -> a + c ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _hpos h
      rw [Nat.zero_add]
      rw [Nat.sub_zero] at h
      exact h
  | succ a ih =>
      cases b with
      | zero =>
          intro hpos h
          rw [Nat.zero_sub] at h
          have impossible : 0 < 0 := Nat.lt_of_lt_of_le hpos h
          exact False.elim (Nat.lt_irrefl 0 impossible)
      | succ b =>
          intro hpos h
          have subLe : c ≤ b - a := by
            rw [Nat.succ_sub_succ] at h
            exact h
          rw [Nat.succ_add]
          exact Nat.succ_le_succ (ih b hpos subLe)

private theorem natSelfLtSubIffAddLt (a b : Nat) :
    a < b - a ↔ a + a < b := by
  constructor
  · intro h
    have addLe : a + Nat.succ a ≤ b :=
      natPosLeSubToAddLe a (Nat.succ a) b (Nat.zero_lt_succ a) h
    rw [Nat.add_succ] at addLe
    exact addLe
  · intro h
    apply natAddLeToLeSub a (Nat.succ a) b
    rw [Nat.add_succ]
    exact h

private theorem natAddSubCancelLeft (a c : Nat) :
    (a + c) - a = c := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      rw [Nat.sub_zero]
  | succ a ih =>
      rw [Nat.succ_add]
      rw [Nat.succ_sub_succ]
      exact ih

private theorem natSubAddCancelOfLe (a b : Nat) :
    a ≤ b -> b - a + a = b := by
  induction a generalizing b with
  | zero =>
      intro _h
      rw [Nat.sub_zero]
      rw [Nat.add_zero]
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          exact False.elim (Nat.not_succ_le_zero _ h)
      | succ b =>
          intro h
          rw [Nat.succ_sub_succ]
          rw [Nat.add_succ]
          exact congrArg Nat.succ (ih b (Nat.succ_le_succ_iff.mp h))

theorem properDivisorSumNat_eq_sigma_sub_self (entries : List BHist) :
    ProperDivisorSumNat entries =
      sigmaFactorsNat entries - bwordLength (factorListProductFn entries) := by
  rfl

theorem sigma_abundant_iff_proper_sum_gt_self (entries : List BHist) :
    IsAbundant entries ↔
      bwordLength (factorListProductFn entries) < ProperDivisorSumNat entries := by
  unfold IsAbundant ProperDivisorSumNat
  constructor
  · intro sigmaLarge
    have addLarge :
        bwordLength (factorListProductFn entries) +
            bwordLength (factorListProductFn entries) <
          sigmaFactorsNat entries := by
      rw [Nat.two_mul] at sigmaLarge
      exact sigmaLarge
    exact (natSelfLtSubIffAddLt _ _).mpr addLarge
  · intro sumLarge
    have addLarge :
        bwordLength (factorListProductFn entries) +
            bwordLength (factorListProductFn entries) <
          sigmaFactorsNat entries :=
      (natSelfLtSubIffAddLt _ _).mp sumLarge
    rw [Nat.two_mul]
    exact addLarge

theorem sigma_perfect_iff_proper_sum_eq_self (entries : List BHist)
    (coversSelf : bwordLength (factorListProductFn entries) ≤ sigmaFactorsNat entries) :
    IsPerfect entries ↔
      ProperDivisorSumNat entries = bwordLength (factorListProductFn entries) := by
  unfold IsPerfect ProperDivisorSumNat
  constructor
  · intro sigmaEq
    calc
      sigmaFactorsNat entries - bwordLength (factorListProductFn entries)
          = (2 * bwordLength (factorListProductFn entries)) -
              bwordLength (factorListProductFn entries) := by
            rw [sigmaEq]
      _ = (bwordLength (factorListProductFn entries) +
              bwordLength (factorListProductFn entries)) -
            bwordLength (factorListProductFn entries) := by
            rw [Nat.two_mul]
      _ = bwordLength (factorListProductFn entries) :=
            natAddSubCancelLeft _ _
  · intro sumEq
    have addEq :
        (sigmaFactorsNat entries - bwordLength (factorListProductFn entries)) +
            bwordLength (factorListProductFn entries) =
          sigmaFactorsNat entries :=
      natSubAddCancelOfLe _ _ coversSelf
    calc
      sigmaFactorsNat entries =
          (sigmaFactorsNat entries - bwordLength (factorListProductFn entries)) +
              bwordLength (factorListProductFn entries) :=
        addEq.symm
      _ = bwordLength (factorListProductFn entries) +
          bwordLength (factorListProductFn entries) := by
        rw [sumEq]
      _ = 2 * bwordLength (factorListProductFn entries) := (Nat.two_mul _).symm

theorem abundance_trichotomy (entries : List BHist) :
    IsAbundant entries ∨ IsDeficient entries ∨ IsPerfect entries := by
  unfold IsAbundant IsDeficient IsPerfect
  cases Nat.lt_trichotomy
      (sigmaFactorsNat entries)
      (2 * bwordLength (factorListProductFn entries)) with
  | inl deficient =>
      exact Or.inr (Or.inl deficient)
  | inr notDeficient =>
      cases notDeficient with
      | inl perfect =>
          exact Or.inr (Or.inr perfect)
      | inr abundant =>
          exact Or.inl abundant

theorem abundance_exclusive (entries : List BHist) :
    (IsAbundant entries -> IsDeficient entries -> False) ∧
      (IsAbundant entries -> IsPerfect entries -> False) ∧
      (IsDeficient entries -> IsPerfect entries -> False) := by
  unfold IsAbundant IsDeficient IsPerfect
  constructor
  · intro abundant deficient
    exact Nat.lt_asymm deficient abundant
  · constructor
    · intro abundant perfect
      exact Nat.lt_irrefl _ (perfect ▸ abundant)
    · intro deficient perfect
      exact Nat.lt_irrefl _ (perfect.symm ▸ deficient)

theorem abundance_classification_total (entries : List BHist) :
    FactorizationNumberClass entries := by
  exact abundance_trichotomy entries

theorem abundance_classification_readback (entries : List BHist) :
    (FactorizationNumberClass entries) ∧
      ((IsAbundant entries -> IsDeficient entries -> False) ∧
        (IsAbundant entries -> IsPerfect entries -> False) ∧
        (IsDeficient entries -> IsPerfect entries -> False)) := by
  exact And.intro (abundance_classification_total entries)
    (abundance_exclusive entries)

abbrev unaryTwo : BHist :=
  natToUnary 2

abbrev unaryThree : BHist :=
  natToUnary 3

abbrev unarySix : BHist :=
  natToUnary 6

abbrev unaryEight : BHist :=
  natToUnary 8

abbrev unaryTwelve : BHist :=
  natToUnary 12

theorem unaryTwo_prime : NatPrime unaryTwo := by
  exact NatPrime_first_pair.left

theorem unaryThree_prime : NatPrime unaryThree := by
  exact NatPrime_first_pair.right

def entriesSix : List BHist :=
  [unaryTwo, unaryThree]

def entriesEight : List BHist :=
  [unaryTwo, unaryTwo, unaryTwo]

def entriesTwelve : List BHist :=
  [unaryTwo, unaryTwo, unaryThree]

private theorem primeFactorizationProduct_singleton_two :
    PrimeFactorizationProduct [unaryTwo] unaryTwo := by
  unfold unaryTwo
  change NatPrime (natToUnary 2) ∧
    ∃ tailProduct : BHist,
      PrimeFactorizationProduct [] tailProduct ∧
        NatMul (natToUnary 2) tailProduct (natToUnary 2)
  exact And.intro NatPrime_first_pair.left
    ⟨natToUnary 1, rfl, by simpa using natToUnary_mul_rel 2 1⟩

private theorem primeFactorizationProduct_singleton_three :
    PrimeFactorizationProduct [unaryThree] unaryThree := by
  unfold unaryThree
  change NatPrime (natToUnary 3) ∧
    ∃ tailProduct : BHist,
      PrimeFactorizationProduct [] tailProduct ∧
        NatMul (natToUnary 3) tailProduct (natToUnary 3)
  exact And.intro NatPrime_first_pair.right
    ⟨natToUnary 1, rfl, by simpa using natToUnary_mul_rel 3 1⟩

private theorem primeFactorizationProduct_two_three :
    PrimeFactorizationProduct entriesSix unarySix := by
  unfold entriesSix unarySix unaryTwo unaryThree
  change NatPrime (natToUnary 2) ∧
    ∃ tailProduct : BHist,
      PrimeFactorizationProduct [natToUnary 3] tailProduct ∧
        NatMul (natToUnary 2) tailProduct (natToUnary 6)
  exact And.intro NatPrime_first_pair.left
    ⟨natToUnary 3, primeFactorizationProduct_singleton_three,
      by simpa using natToUnary_mul_rel 2 3⟩

private theorem primeFactorizationProduct_two_two :
    PrimeFactorizationProduct [unaryTwo, unaryTwo] (natToUnary 4) := by
  unfold unaryTwo
  change NatPrime (natToUnary 2) ∧
    ∃ tailProduct : BHist,
      PrimeFactorizationProduct [natToUnary 2] tailProduct ∧
        NatMul (natToUnary 2) tailProduct (natToUnary 4)
  exact And.intro NatPrime_first_pair.left
    ⟨natToUnary 2, primeFactorizationProduct_singleton_two,
      by simpa using natToUnary_mul_rel 2 2⟩

private theorem primeFactorizationProduct_two_two_two :
    PrimeFactorizationProduct entriesEight unaryEight := by
  unfold entriesEight unaryEight unaryTwo
  change NatPrime (natToUnary 2) ∧
    ∃ tailProduct : BHist,
      PrimeFactorizationProduct [natToUnary 2, natToUnary 2] tailProduct ∧
        NatMul (natToUnary 2) tailProduct (natToUnary 8)
  exact And.intro NatPrime_first_pair.left
    ⟨natToUnary 4, primeFactorizationProduct_two_two,
      by simpa using natToUnary_mul_rel 2 4⟩

private theorem primeFactorizationProduct_two_two_three :
    PrimeFactorizationProduct entriesTwelve unaryTwelve := by
  unfold entriesTwelve unaryTwelve unaryTwo unaryThree
  change NatPrime (natToUnary 2) ∧
    ∃ tailProduct : BHist,
      PrimeFactorizationProduct [natToUnary 2, natToUnary 3] tailProduct ∧
        NatMul (natToUnary 2) tailProduct (natToUnary 12)
  exact And.intro NatPrime_first_pair.left
    ⟨natToUnary 6, primeFactorizationProduct_two_three,
      by simpa using natToUnary_mul_rel 2 6⟩

theorem six_factorization : PrimeFactorization unarySix entriesSix := by
  exact And.intro (natToUnary_unary 6) primeFactorizationProduct_two_three

theorem eight_factorization : PrimeFactorization unaryEight entriesEight := by
  exact And.intro (natToUnary_unary 8) primeFactorizationProduct_two_two_two

theorem twelve_factorization : PrimeFactorization unaryTwelve entriesTwelve := by
  exact And.intro (natToUnary_unary 12) primeFactorizationProduct_two_two_three

theorem entriesSix_product_length :
    bwordLength (factorListProductFn entriesSix) = 6 := by
  rfl

theorem entriesEight_product_length :
    bwordLength (factorListProductFn entriesEight) = 8 := by
  rfl

theorem entriesTwelve_product_length :
    bwordLength (factorListProductFn entriesTwelve) = 12 := by
  rfl

theorem entriesSix_sigma :
    sigmaFactorsNat entriesSix = 12 := by
  rfl

theorem entriesEight_sigma :
    sigmaFactorsNat entriesEight = 15 := by
  rfl

theorem entriesTwelve_sigma :
    sigmaFactorsNat entriesTwelve = 28 := by
  rfl

theorem six_divisorSigmaOfFactorization :
    DivisorSigmaOfFactorization unarySix (natToUnary 12) := by
  refine ⟨entriesSix, six_factorization, ?_⟩
  unfold sigmaFactors
  rw [entriesSix_sigma]
  exact hsame_refl _

theorem eight_divisorSigmaOfFactorization :
    DivisorSigmaOfFactorization unaryEight (natToUnary 15) := by
  refine ⟨entriesEight, eight_factorization, ?_⟩
  unfold sigmaFactors
  rw [entriesEight_sigma]
  exact hsame_refl _

theorem twelve_divisorSigmaOfFactorization :
    DivisorSigmaOfFactorization unaryTwelve (natToUnary 28) := by
  refine ⟨entriesTwelve, twelve_factorization, ?_⟩
  unfold sigmaFactors
  rw [entriesTwelve_sigma]
  exact hsame_refl _

theorem entriesSix_properDivisorSum :
    ProperDivisorSumNat entriesSix = 6 := by
  rfl

theorem entriesEight_properDivisorSum :
    ProperDivisorSumNat entriesEight = 7 := by
  rfl

theorem entriesTwelve_properDivisorSum :
    ProperDivisorSumNat entriesTwelve = 16 := by
  rfl

theorem six_properDivisorSumOfFactorization :
    ProperDivisorSumOfFactorization unarySix 6 := by
  exact ⟨entriesSix, six_factorization, entriesSix_properDivisorSum.symm⟩

theorem eight_properDivisorSumOfFactorization :
    ProperDivisorSumOfFactorization unaryEight 7 := by
  exact ⟨entriesEight, eight_factorization, entriesEight_properDivisorSum.symm⟩

theorem twelve_properDivisorSumOfFactorization :
    ProperDivisorSumOfFactorization unaryTwelve 16 := by
  exact ⟨entriesTwelve, twelve_factorization, entriesTwelve_properDivisorSum.symm⟩

theorem perfect_six : IsPerfect entriesSix := by
  rfl

theorem deficient_eight : IsDeficient entriesEight := by
  unfold IsDeficient entriesEight unaryTwo
  decide

theorem abundant_twelve : IsAbundant entriesTwelve := by
  unfold IsAbundant entriesTwelve unaryTwo unaryThree
  decide

theorem six_classification :
    FactorizationNumberClass entriesSix := by
  exact Or.inr (Or.inr perfect_six)

theorem eight_classification :
    FactorizationNumberClass entriesEight := by
  exact Or.inr (Or.inl deficient_eight)

theorem twelve_classification :
    FactorizationNumberClass entriesTwelve := by
  exact Or.inl abundant_twelve

def integerUp_rel_comm_ring_available :
    BEDC.Algebra.Rel.RelCommRing
      BEDC.Algebra.Rel.IntegerUp BEDC.Algebra.Rel.IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

theorem integerUp_sub_uses_rel_comm_ring
    (x y : BEDC.Algebra.Rel.IntegerUp) :
    BEDC.Algebra.Rel.IntEq
      (BEDC.Algebra.Rel.IntegerUp_RelCommRing.sub x y)
      (BEDC.Algebra.Rel.IntAdd x (BEDC.Algebra.Rel.IntNeg y)) :=
  BEDC.Algebra.Rel.IntegerUp_sub_eq_add_neg x y

end BEDC.Derived.AbundanceUp
