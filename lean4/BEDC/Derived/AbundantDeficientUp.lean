import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.AbundanceUp

namespace BEDC.Derived.AbundantDeficientUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp

def sigmaNat (profile : PrimePowerProfile) : Nat :=
  divisorSigmaProfileNat 1 profile

def profileValueNat : PrimePowerProfile -> Nat
  | [] => 1
  | e :: es => natPow (bwordLength e.prime) e.exponent * profileValueNat es

def properDivisorSumNat (profile : PrimePowerProfile) : Nat :=
  sigmaNat profile - profileValueNat profile

def IsAbundantProfile (profile : PrimePowerProfile) : Prop :=
  2 * profileValueNat profile < sigmaNat profile

def IsDeficientProfile (profile : PrimePowerProfile) : Prop :=
  sigmaNat profile < 2 * profileValueNat profile

def IsPerfectProfile (profile : PrimePowerProfile) : Prop :=
  sigmaNat profile = 2 * profileValueNat profile

def NumberClassProfile (profile : PrimePowerProfile) : Prop :=
  IsAbundantProfile profile ∨ IsDeficientProfile profile ∨ IsPerfectProfile profile

def SigmaOneOfProfile (n sigma : BHist) (profile : PrimePowerProfile) : Prop :=
  DivisorSigmaOfProfile 1 n sigma profile

def ProperDivisorSumOfProfile (n s : BHist) (profile : PrimePowerProfile) : Prop :=
  ∃ sigma : BHist,
    SigmaOneOfProfile n sigma profile ∧
      hsame s (natToUnary (properDivisorSumNat profile))

def AbundantNumber (n : BHist) : Prop :=
  ∃ profile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      IsAbundantProfile profile

def DeficientNumber (n : BHist) : Prop :=
  ∃ profile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      IsDeficientProfile profile

def PerfectNumber (n : BHist) : Prop :=
  ∃ profile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      IsPerfectProfile profile

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem nat_left_distrib_pure (a b c : Nat) :
    a * (b + c) = a * b + a * c := by
  rw [Nat.mul_add]

private theorem nat_mul_pos_pure {a b : Nat} :
    0 < a -> 0 < b -> 0 < a * b := by
  intro ha hb
  exact Nat.mul_pos ha hb

private theorem nat_mul_lt_mul_pos_left {a b c : Nat} :
    0 < c -> a < b -> c * a < c * b := by
  intro hpos hlt
  exact Nat.mul_lt_mul_of_pos_left hlt hpos

private theorem nat_two_mul (n : Nat) :
    2 * n = n + n := by
  rw [Nat.two_mul]

theorem sigmaNat_eq_divisorSigmaProfileNat (profile : PrimePowerProfile) :
    sigmaNat profile = divisorSigmaProfileNat 1 profile := by
  rfl

theorem properDivisorSumNat_eq_sigma_sub_self (profile : PrimePowerProfile) :
    properDivisorSumNat profile = sigmaNat profile - profileValueNat profile := by
  rfl

theorem profileValueNat_append
    (xs ys : PrimePowerProfile) :
    profileValueNat (xs ++ ys) = profileValueNat xs * profileValueNat ys := by
  induction xs with
  | nil =>
      change profileValueNat ys = 1 * profileValueNat ys
      rw [Nat.one_mul]
  | cons e es ih =>
      change
        natPow (bwordLength e.prime) e.exponent * profileValueNat (es ++ ys) =
          (natPow (bwordLength e.prime) e.exponent * profileValueNat es) *
            profileValueNat ys
      rw [ih]
      exact (nat_mul_assoc_pure
        (natPow (bwordLength e.prime) e.exponent)
        (profileValueNat es)
        (profileValueNat ys)).symm

theorem classification_trichotomy (profile : PrimePowerProfile) :
    NumberClassProfile profile := by
  unfold NumberClassProfile IsAbundantProfile IsDeficientProfile IsPerfectProfile
  cases Nat.lt_trichotomy (sigmaNat profile) (2 * profileValueNat profile) with
  | inl deficient =>
      exact Or.inr (Or.inl deficient)
  | inr rest =>
      cases rest with
      | inl perfect =>
          exact Or.inr (Or.inr perfect)
      | inr abundant =>
          exact Or.inl abundant

theorem classification_exclusive (profile : PrimePowerProfile) :
    (IsAbundantProfile profile -> IsDeficientProfile profile -> False) ∧
      (IsAbundantProfile profile -> IsPerfectProfile profile -> False) ∧
      (IsDeficientProfile profile -> IsPerfectProfile profile -> False) := by
  unfold IsAbundantProfile IsDeficientProfile IsPerfectProfile
  constructor
  · intro abundant deficient
    exact Nat.lt_asymm deficient abundant
  · constructor
    · intro abundant perfect
      exact Nat.lt_irrefl _ (perfect ▸ abundant)
    · intro deficient perfect
      exact Nat.lt_irrefl _ (perfect.symm ▸ deficient)

theorem classification_total_with_exclusion (profile : PrimePowerProfile) :
    NumberClassProfile profile ∧
      (IsAbundantProfile profile -> IsDeficientProfile profile -> False) ∧
        (IsAbundantProfile profile -> IsPerfectProfile profile -> False) ∧
          (IsDeficientProfile profile -> IsPerfectProfile profile -> False) := by
  exact ⟨classification_trichotomy profile, classification_exclusive profile⟩

def NatOne : BHist := natToUnary 1
def NatTwo : BHist := natToUnary 2
def NatThree : BHist := natToUnary 3
def NatSix : BHist := natToUnary 6
def NatEight : BHist := natToUnary 8
def NatTwelve : BHist := natToUnary 12
def NatFifteen : BHist := natToUnary 15
def NatTwentyEight : BHist := natToUnary 28

theorem NatOne_unary : UnaryHistory NatOne := by
  unfold NatOne
  exact natToUnary_unary 1

theorem NatTwo_prime : NatPrime NatTwo := by
  unfold NatTwo
  exact NatPrime_first_pair.left

theorem NatThree_prime : NatPrime NatThree := by
  unfold NatThree
  exact NatPrime_first_pair.right

def profileSix : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 1 }, { prime := NatThree, exponent := 1 }]

def profileEight : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 3 }]

def profileTwelve : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 2 }, { prime := NatThree, exponent := 1 }]

theorem profileSix_valid : ProfileValid profileSix := by
  unfold profileSix
  exact ProfileValid.cons NatTwo_prime
    (by intro h; cases h)
    rfl
    (ProfileValid.cons NatThree_prime
      (by intro h; cases h)
      rfl
      ProfileValid.nil)

theorem profileEight_valid : ProfileValid profileEight := by
  unfold profileEight
  exact ProfileValid.cons NatTwo_prime
    (by intro h; cases h)
    rfl
    ProfileValid.nil

theorem profileTwelve_valid : ProfileValid profileTwelve := by
  unfold profileTwelve
  exact ProfileValid.cons NatTwo_prime
    (by intro h; cases h)
    rfl
    (ProfileValid.cons NatThree_prime
      (by intro h; cases h)
      rfl
      ProfileValid.nil)

theorem profileSix_value : profileValueNat profileSix = 6 := by
  rfl

theorem profileEight_value : profileValueNat profileEight = 8 := by
  rfl

theorem profileTwelve_value : profileValueNat profileTwelve = 12 := by
  rfl

theorem sigmaSix_value : sigmaNat profileSix = 12 := by
  rfl

theorem sigmaEight_value : sigmaNat profileEight = 15 := by
  rfl

theorem sigmaTwelve_value : sigmaNat profileTwelve = 28 := by
  rfl

theorem properDivisorSumSix_value :
    properDivisorSumNat profileSix = 6 := by
  rfl

theorem properDivisorSumEight_value :
    properDivisorSumNat profileEight = 7 := by
  rfl

theorem properDivisorSumTwelve_value :
    properDivisorSumNat profileTwelve = 16 := by
  rfl

theorem six_perfect_profile : IsPerfectProfile profileSix := by
  unfold IsPerfectProfile sigmaNat profileSix profileValueNat
  rfl

theorem eight_deficient_profile : IsDeficientProfile profileEight := by
  unfold IsDeficientProfile sigmaNat profileEight profileValueNat
  decide

theorem twelve_abundant_profile : IsAbundantProfile profileTwelve := by
  unfold IsAbundantProfile sigmaNat profileTwelve profileValueNat
  decide

theorem six_classification_profile : NumberClassProfile profileSix := by
  exact Or.inr (Or.inr six_perfect_profile)

theorem eight_classification_profile : NumberClassProfile profileEight := by
  exact Or.inr (Or.inl eight_deficient_profile)

theorem twelve_classification_profile : NumberClassProfile profileTwelve := by
  exact Or.inl twelve_abundant_profile

theorem six_sigma_checked :
    SigmaOneOfProfile NatSix NatTwelve profileSix := by
  unfold SigmaOneOfProfile NatSix NatTwelve
  exact ⟨profileSix_valid, BEDC.Derived.AbundanceUp.six_factorization, hsame_refl _⟩

theorem eight_sigma_checked :
    SigmaOneOfProfile NatEight NatFifteen profileEight := by
  unfold SigmaOneOfProfile NatEight NatFifteen
  exact ⟨profileEight_valid, BEDC.Derived.AbundanceUp.eight_factorization, hsame_refl _⟩

theorem twelve_sigma_checked :
    SigmaOneOfProfile NatTwelve NatTwentyEight profileTwelve := by
  unfold SigmaOneOfProfile NatTwelve NatTwentyEight
  exact ⟨profileTwelve_valid, BEDC.Derived.AbundanceUp.twelve_factorization, hsame_refl _⟩

theorem six_properDivisorSum_checked :
    ProperDivisorSumOfProfile NatSix NatSix profileSix := by
  unfold ProperDivisorSumOfProfile
  exact ⟨NatTwelve, six_sigma_checked, hsame_refl _⟩

theorem eight_properDivisorSum_checked :
    ProperDivisorSumOfProfile NatEight (natToUnary 7) profileEight := by
  unfold ProperDivisorSumOfProfile
  exact ⟨NatFifteen, eight_sigma_checked, hsame_refl _⟩

theorem twelve_properDivisorSum_checked :
    ProperDivisorSumOfProfile NatTwelve (natToUnary 16) profileTwelve := by
  unfold ProperDivisorSumOfProfile
  exact ⟨NatTwentyEight, twelve_sigma_checked, hsame_refl _⟩

theorem perfect_six_number : PerfectNumber NatSix := by
  exact ⟨profileSix, profileSix_valid, BEDC.Derived.AbundanceUp.six_factorization,
    six_perfect_profile⟩

theorem deficient_eight_number : DeficientNumber NatEight := by
  exact ⟨profileEight, profileEight_valid, BEDC.Derived.AbundanceUp.eight_factorization,
    eight_deficient_profile⟩

theorem abundant_twelve_number : AbundantNumber NatTwelve := by
  exact ⟨profileTwelve, profileTwelve_valid,
    BEDC.Derived.AbundanceUp.twelve_factorization, twelve_abundant_profile⟩

theorem sigmaPowerFactorNat_one_step
    (p : BHist) (a : Nat) :
    divisorSigmaPowerFactorNat 1 p (a + 1) =
      divisorSigmaPowerFactorNat 1 p a + natPow (bwordLength p) (a + 1) := by
  change
    divisorSigmaPowerFactorNat 1 p a + natPow (bwordLength p) (1 * (a + 1)) =
      divisorSigmaPowerFactorNat 1 p a + natPow (bwordLength p) (a + 1)
  rw [Nat.one_mul]

theorem sigmaPowerFactorNat_one_positive (p : BHist) :
    ∀ a : Nat, 0 < divisorSigmaPowerFactorNat 1 p a
  | 0 => Nat.zero_lt_succ 0
  | a + 1 => by
      rw [sigmaPowerFactorNat_one_step]
      exact Nat.lt_of_lt_of_le
        (sigmaPowerFactorNat_one_positive p a)
        (Nat.le_add_right
          (divisorSigmaPowerFactorNat 1 p a)
          (natPow (bwordLength p) (a + 1)))

theorem natPow_pos_of_base_pos {base : Nat} :
    0 < base -> ∀ exp : Nat, 0 < natPow base exp
  | basePos, 0 => Nat.zero_lt_succ 0
  | basePos, exp + 1 => by
      unfold natPow
      exact nat_mul_pos_pure basePos (natPow_pos_of_base_pos basePos exp)

theorem natPow_succ_mul (base exp : Nat) :
    natPow base (exp + 1) = base * natPow base exp := by
  rfl

theorem natPow_add (base a q : Nat) :
    natPow base (a + q) = natPow base a * natPow base q := by
  induction q with
  | zero =>
      rw [Nat.add_zero]
      change natPow base a = natPow base a * 1
      rw [Nat.mul_one]
  | succ q ih =>
      rw [Nat.add_succ]
      change base * natPow base (a + q) = natPow base a * (base * natPow base q)
      rw [ih]
      calc
        base * (natPow base a * natPow base q) =
            (base * natPow base a) * natPow base q := (nat_mul_assoc_pure _ _ _).symm
        _ = (natPow base a * base) * natPow base q := by
          rw [Nat.mul_comm base (natPow base a)]
        _ = natPow base a * (base * natPow base q) := nat_mul_assoc_pure _ _ _

theorem prime_length_positive {p : BHist} :
    NatPrime p -> 0 < bwordLength p := by
  intro hp
  have unitLt :
      bwordLength (BHist.e1 BHist.Empty) < bwordLength p :=
    NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) hp.right.left
  change 1 < bwordLength p at unitLt
  exact Nat.lt_trans (by decide : 0 < 1) unitLt

theorem sigmaPowerFactorNat_one_ge_value
    (p : BHist) :
    ∀ a : Nat, natPow (bwordLength p) a ≤ divisorSigmaPowerFactorNat 1 p a
  | 0 => Nat.le_refl 1
  | a + 1 => by
      rw [sigmaPowerFactorNat_one_step]
      exact Nat.le_add_left
        (natPow (bwordLength p) (a + 1))
        (divisorSigmaPowerFactorNat 1 p a)

theorem sigmaPowerFactorNat_one_scale_le
    (p : BHist) (q : Nat) :
    ∀ a : Nat,
      natPow (bwordLength p) q * divisorSigmaPowerFactorNat 1 p a ≤
        divisorSigmaPowerFactorNat 1 p (a + q)
  | 0 => by
      rw [show divisorSigmaPowerFactorNat 1 p 0 = 1 by rfl,
        Nat.mul_one, Nat.zero_add]
      exact sigmaPowerFactorNat_one_ge_value p q
  | a + 1 => by
      have powShift :
          natPow (bwordLength p) q * natPow (bwordLength p) (a + 1) =
            natPow (bwordLength p) ((a + q) + 1) := by
        calc
          natPow (bwordLength p) q * natPow (bwordLength p) (a + 1) =
              natPow (bwordLength p) (q + (a + 1)) :=
            (natPow_add (bwordLength p) q (a + 1)).symm
          _ = natPow (bwordLength p) ((a + q) + 1) := by
            have argEq : q + (a + 1) = a + q + 1 := by
              calc
                q + (a + 1) = q + a + 1 := (Nat.add_assoc q a 1).symm
                _ = a + q + 1 := by rw [Nat.add_comm q a]
            exact congrArg (fun n => natPow (bwordLength p) n) argEq
      calc
        natPow (bwordLength p) q * divisorSigmaPowerFactorNat 1 p (a + 1)
            =
            natPow (bwordLength p) q *
              (divisorSigmaPowerFactorNat 1 p a +
                natPow (bwordLength p) (a + 1)) := by
          rw [sigmaPowerFactorNat_one_step]
        _ =
            natPow (bwordLength p) q * divisorSigmaPowerFactorNat 1 p a +
              natPow (bwordLength p) q * natPow (bwordLength p) (a + 1) := by
          rw [Nat.mul_add]
        _ ≤
            divisorSigmaPowerFactorNat 1 p (a + q) +
              natPow (bwordLength p) ((a + q) + 1) := by
          exact Nat.add_le_add (sigmaPowerFactorNat_one_scale_le p q a)
            (Nat.le_of_eq powShift)
        _ =
            divisorSigmaPowerFactorNat 1 p ((a + 1) + q) := by
          rw [Nat.succ_add, sigmaPowerFactorNat_one_step]

theorem profileValueNat_extend_head
    (e : PrimePowerEntry) (es : PrimePowerProfile) (q : Nat) :
    profileValueNat ({ prime := e.prime, exponent := e.exponent + q } :: es) =
      natPow (bwordLength e.prime) (e.exponent + q) * profileValueNat es := by
  rfl

theorem sigmaNat_extend_head
    (e : PrimePowerEntry) (es : PrimePowerProfile) (q : Nat) :
    sigmaNat ({ prime := e.prime, exponent := e.exponent + q } :: es) =
      divisorSigmaPowerFactorNat 1 e.prime (e.exponent + q) *
        divisorSigmaProfileNat 1 es := by
  rfl

theorem sigmaNat_append
    (xs ys : PrimePowerProfile) :
    sigmaNat (xs ++ ys) = sigmaNat xs * sigmaNat ys := by
  unfold sigmaNat
  exact divisorSigmaProfileNat_append 1 xs ys

theorem sigmaNat_positive (profile : PrimePowerProfile) :
    0 < sigmaNat profile := by
  induction profile with
  | nil =>
      unfold sigmaNat
      exact Nat.zero_lt_succ 0
  | cons e es ih =>
      unfold sigmaNat
      exact nat_mul_pos_pure (sigmaPowerFactorNat_one_positive e.prime e.exponent) ih

theorem profileValueNat_le_sigmaNat (profile : PrimePowerProfile) :
    profileValueNat profile ≤ sigmaNat profile := by
  induction profile with
  | nil =>
      unfold profileValueNat sigmaNat
      exact Nat.le_refl 1
  | cons e es ih =>
      unfold profileValueNat sigmaNat
      exact Nat.mul_le_mul
        (sigmaPowerFactorNat_one_ge_value e.prime e.exponent) ih

theorem abundant_profile_append_positive
    {xs ys : PrimePowerProfile} :
    IsAbundantProfile xs ->
      IsAbundantProfile (xs ++ ys) := by
  intro abundant
  unfold IsAbundantProfile at abundant ⊢
  rw [profileValueNat_append, sigmaNat_append]
  have scaled :
      sigmaNat ys * (2 * profileValueNat xs) <
        sigmaNat ys * sigmaNat xs :=
    nat_mul_lt_mul_pos_left (sigmaNat_positive ys) abundant
  have valueLeSigma : profileValueNat ys ≤ sigmaNat ys := by
    exact profileValueNat_le_sigmaNat ys
  have leftBound :
      2 * (profileValueNat xs * profileValueNat ys) ≤
        sigmaNat ys * (2 * profileValueNat xs) := by
    calc
      2 * (profileValueNat xs * profileValueNat ys)
          = (2 * profileValueNat xs) * profileValueNat ys := by
            exact (nat_mul_assoc_pure 2 (profileValueNat xs) (profileValueNat ys)).symm
      _ = profileValueNat ys * (2 * profileValueNat xs) := by
            rw [Nat.mul_comm]
      _ ≤ sigmaNat ys * (2 * profileValueNat xs) :=
            Nat.mul_le_mul_right (2 * profileValueNat xs) valueLeSigma
  have rightComm :
      sigmaNat ys * sigmaNat xs = sigmaNat xs * sigmaNat ys := by
    rw [Nat.mul_comm]
  exact Nat.lt_of_le_of_lt leftBound (rightComm ▸ scaled)

theorem abundant_profile_append_multiplier
    {xs ys : PrimePowerProfile} :
    IsAbundantProfile xs ->
      ProfileValid ys ->
        IsAbundantProfile (xs ++ ys) := by
  intro abundant _validY
  exact abundant_profile_append_positive abundant

theorem abundant_number_coprime_profile_multiple
    {m n mn : BHist} {xs ys : PrimePowerProfile} :
    ProfileValid xs -> ProfileValid ys ->
      listNoCommonPrime (profilePrimes xs) (profilePrimes ys) ->
        PrimeFactorization m (expandProfile xs) ->
          PrimeFactorization n (expandProfile ys) ->
            NatMul m n mn ->
              IsAbundantProfile xs ->
                AbundantNumber mn := by
  intro validX validY disjoint factorX factorY mul abundantX
  have product :
      PrimeFactorizationProduct (expandProfile (xs ++ ys)) mn :=
    PrimeFactorizationProduct_profile_append_mul factorX.right factorY.right mul
  have factorMN : PrimeFactorization mn (expandProfile (xs ++ ys)) :=
    ⟨NatMul_result_unary factorX.left mul, product⟩
  exact ⟨xs ++ ys,
    ProfileValid_append_disjoint validX validY disjoint,
    factorMN,
    abundant_profile_append_multiplier abundantX validY⟩

theorem abundant_prime_power_multiple_profile
    {e : PrimePowerEntry} {es : PrimePowerProfile} {q : Nat} :
    NatPrime e.prime -> 0 < q ->
      IsAbundantProfile (e :: es) ->
        IsAbundantProfile ({ prime := e.prime, exponent := e.exponent + q } :: es) := by
  intro pPrime qPos abundant
  unfold IsAbundantProfile sigmaNat profileValueNat at abundant ⊢
  let scale := natPow (bwordLength e.prime) q
  have scalePositive : 0 < scale :=
    natPow_pos_of_base_pos (prime_length_positive pPrime) q
  have scaledAbundant :
      scale *
          (2 * (natPow (bwordLength e.prime) e.exponent * profileValueNat es)) <
        scale *
          (divisorSigmaPowerFactorNat 1 e.prime e.exponent *
            divisorSigmaProfileNat 1 es) :=
    nat_mul_lt_mul_pos_left scalePositive abundant
  have leftScale :
      scale *
          (2 * (natPow (bwordLength e.prime) e.exponent * profileValueNat es)) =
        2 * (natPow (bwordLength e.prime) (e.exponent + q) *
          profileValueNat es) := by
    unfold scale
    calc
      natPow (bwordLength e.prime) q *
          (2 * (natPow (bwordLength e.prime) e.exponent * profileValueNat es))
          =
          (natPow (bwordLength e.prime) q * 2) *
            (natPow (bwordLength e.prime) e.exponent * profileValueNat es) :=
        (nat_mul_assoc_pure _ _ _).symm
      _ =
          (2 * natPow (bwordLength e.prime) q) *
            (natPow (bwordLength e.prime) e.exponent * profileValueNat es) := by
        rw [Nat.mul_comm (natPow (bwordLength e.prime) q) 2]
      _ =
          2 * (natPow (bwordLength e.prime) q *
            (natPow (bwordLength e.prime) e.exponent * profileValueNat es)) :=
        nat_mul_assoc_pure _ _ _
      _ =
          2 * ((natPow (bwordLength e.prime) q *
            natPow (bwordLength e.prime) e.exponent) * profileValueNat es) := by
        exact congrArg (fun z => 2 * z)
          (nat_mul_assoc_pure
            (natPow (bwordLength e.prime) q)
            (natPow (bwordLength e.prime) e.exponent)
            (profileValueNat es)).symm
      _ =
          2 * (natPow (bwordLength e.prime) (q + e.exponent) *
            profileValueNat es) := by
        rw [natPow_add]
      _ =
          2 * (natPow (bwordLength e.prime) (e.exponent + q) *
            profileValueNat es) := by
        rw [Nat.add_comm q e.exponent]
  have rightScale :
      scale *
          (divisorSigmaPowerFactorNat 1 e.prime e.exponent *
            divisorSigmaProfileNat 1 es) ≤
        divisorSigmaPowerFactorNat 1 e.prime (e.exponent + q) *
          divisorSigmaProfileNat 1 es := by
    unfold scale
    calc
      natPow (bwordLength e.prime) q *
          (divisorSigmaPowerFactorNat 1 e.prime e.exponent *
            divisorSigmaProfileNat 1 es)
          =
          (natPow (bwordLength e.prime) q *
            divisorSigmaPowerFactorNat 1 e.prime e.exponent) *
            divisorSigmaProfileNat 1 es := (nat_mul_assoc_pure _ _ _).symm
      _ ≤
          divisorSigmaPowerFactorNat 1 e.prime (e.exponent + q) *
            divisorSigmaProfileNat 1 es :=
        Nat.mul_le_mul_right (divisorSigmaProfileNat 1 es)
          (sigmaPowerFactorNat_one_scale_le e.prime q e.exponent)
  exact leftScale ▸ Nat.lt_of_lt_of_le scaledAbundant rightScale

theorem twelve_times_two_profile_abundant :
    IsAbundantProfile [{ prime := NatTwo, exponent := 3 },
      { prime := NatThree, exponent := 1 }] := by
  have shifted :=
    abundant_prime_power_multiple_profile
      (e := { prime := NatTwo, exponent := 2 })
      (es := [{ prime := NatThree, exponent := 1 }])
      (q := 1)
      NatTwo_prime
      (Nat.zero_lt_succ 0)
      twelve_abundant_profile
  change IsAbundantProfile
    [{ prime := NatTwo, exponent := 2 + 1 },
      { prime := NatThree, exponent := 1 }] at shifted
  exact shifted

def profileThree : PrimePowerProfile :=
  [{ prime := NatThree, exponent := 1 }]

theorem profileThree_valid : ProfileValid profileThree := by
  unfold profileThree
  exact ProfileValid.cons NatThree_prime
    (by intro h; cases h)
    rfl
    ProfileValid.nil

theorem profileThree_value : profileValueNat profileThree = 3 := by
  rfl

theorem sigmaThree_value : sigmaNat profileThree = 4 := by
  rfl

theorem twelve_times_three_profile_abundant :
    IsAbundantProfile (profileTwelve ++ profileThree) := by
  exact abundant_profile_append_multiplier twelve_abundant_profile profileThree_valid

end BEDC.Derived.AbundantDeficientUp
