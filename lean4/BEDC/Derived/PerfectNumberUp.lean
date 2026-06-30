import BEDC.Derived.AbundantDeficientUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.PrimeUp.UniqueFactorization

namespace BEDC.Derived.PerfectNumberUp

set_option maxRecDepth 20000

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length natMulFn natMulFn_rel)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.AbundantDeficientUp

abbrev PerfectNumberBySigmaProfile (n : BHist) : Prop :=
  PerfectNumber n

def powTwoNat : Nat -> Nat
  | 0 => 1
  | k + 1 => 2 * powTwoNat k

def mersenneNat (exponent : Nat) : Nat :=
  powTwoNat exponent - 1

def mersenneHist (exponent : Nat) : BHist :=
  natToUnary (mersenneNat exponent)

def MersennePrimeCriterion (exponent : Nat) : Prop :=
  NatPrime (mersenneHist exponent)

def evenPerfectCandidateNat (k : Nat) : Nat :=
  powTwoNat k * mersenneNat (k + 1)

def evenPerfectCandidate (k : Nat) : BHist :=
  natToUnary (evenPerfectCandidateNat k)

def profilePowerTwo (k : Nat) : PrimePowerProfile :=
  [{ prime := natToUnary 2, exponent := k }]

def profileMersenne (k : Nat) : PrimePowerProfile :=
  [{ prime := mersenneHist (k + 1), exponent := 1 }]

def profileMersenneEven (k : Nat) : PrimePowerProfile :=
  profilePowerTwo k ++ profileMersenne k

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

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem natToUnary_append (m n : Nat) :
    BEDC.FKernel.Cont.append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (BEDC.FKernel.Cont.append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

private theorem natMulFn_natToUnary (m n : Nat) :
    natMulFn (natToUnary m) (natToUnary n) = natToUnary (m * n) := by
  induction n with
  | zero =>
      rw [Nat.mul_zero]
      rfl
  | succ n ih =>
      change BEDC.FKernel.Cont.append
          (natMulFn (natToUnary m) (natToUnary n)) (natToUnary m) =
        natToUnary (m * Nat.succ n)
      rw [ih]
      rw [natToUnary_append]
      rw [Nat.mul_succ]

private theorem natToUnary_mul_rel (m n : Nat) :
    NatMul (natToUnary m) (natToUnary n) (natToUnary (m * n)) := by
  have rel :
      NatMul (natToUnary m) (natToUnary n)
        (natMulFn (natToUnary m) (natToUnary n)) :=
    natMulFn_rel (natToUnary_unary m) (natToUnary_unary n)
  exact (NatMul_result_hsame_transport rel (natMulFn_natToUnary m n)).right

private theorem natToUnary_mul_one_rel (m : Nat) :
    NatMul (natToUnary m) (natToUnary 1) (natToUnary m) := by
  change NatMul (natToUnary m) (BHist.e1 BHist.Empty) (natToUnary m)
  exact NatMul.succ (NatMul.zero (natToUnary_unary m))
    (BEDC.FKernel.Cont.cont_left_unit (natToUnary m))

private theorem natPow_eq_powTwoNat :
    ∀ k : Nat, natPow 2 k = powTwoNat k
  | 0 => rfl
  | k + 1 => by
      change 2 * natPow 2 k = 2 * powTwoNat k
      exact congrArg (fun x => 2 * x) (natPow_eq_powTwoNat k)

private theorem powTwoNat_positive (k : Nat) :
    0 < powTwoNat k := by
  induction k with
  | zero =>
      exact Nat.zero_lt_succ 0
  | succ k ih =>
      change 0 < 2 * powTwoNat k
      exact Nat.mul_pos (by decide : 0 < 2) ih

private theorem nat_one_ne_three :
    1 = 3 -> False := by
  intro h
  change Nat.succ 0 = Nat.succ (Nat.succ (Nat.succ 0)) at h
  have h1 : 0 = Nat.succ (Nat.succ 0) := Nat.succ.inj h
  cases h1

private theorem nat_two_ne_three :
    2 = 3 -> False := by
  intro h
  change Nat.succ (Nat.succ 0) =
    Nat.succ (Nat.succ (Nat.succ 0)) at h
  have h1 : Nat.succ 0 = Nat.succ (Nat.succ 0) := Nat.succ.inj h
  have h2 : 0 = Nat.succ 0 := Nat.succ.inj h1
  cases h2

private theorem two_mul_two_mul_positive_ne_three :
    ∀ n : Nat, 0 < n -> 2 * (2 * n) = 3 -> False
  | 0, pos, _eq => by cases pos
  | Nat.succ x, _pos, eq => by
      change Nat.succ (Nat.succ (Nat.succ (Nat.succ (2 * (2 * x))))) =
        Nat.succ (Nat.succ (Nat.succ 0)) at eq
      have h1 : Nat.succ (Nat.succ (Nat.succ (2 * (2 * x)))) =
          Nat.succ (Nat.succ 0) := Nat.succ.inj eq
      have h2 : Nat.succ (Nat.succ (2 * (2 * x))) = Nat.succ 0 :=
        Nat.succ.inj h1
      have h3 : Nat.succ (2 * (2 * x)) = 0 := Nat.succ.inj h2
      cases h3

private theorem powTwoNat_ne_three :
    ∀ k : Nat, powTwoNat k = 3 -> False
  | 0, eq => nat_one_ne_three eq
  | 1, eq => nat_two_ne_three eq
  | k + 2, eq => by
      change 2 * (2 * powTwoNat k) = 3 at eq
      exact two_mul_two_mul_positive_ne_three
        (powTwoNat k) (powTwoNat_positive k) eq

private theorem nat_pred_add_one (a : Nat) :
    0 < a -> a - 1 + 1 = a := by
  intro pos
  cases a with
  | zero =>
      cases pos
  | succ _ =>
      rfl

private theorem nat_pred_add_self_comm (a : Nat) :
    0 < a -> a - 1 + a = a + a - 1 := by
  intro pos
  cases a with
  | zero =>
      cases pos
  | succ n =>
      change n + Nat.succ n = Nat.succ n + Nat.succ n - 1
      rw [Nat.add_comm n (Nat.succ n)]
      rfl

private theorem natPow_one (base : Nat) :
    natPow base 1 = base := by
  change base * 1 = base
  rw [Nat.mul_one]

private theorem sigmaPowerFactorNat_two_closed :
    ∀ k : Nat,
      divisorSigmaPowerFactorNat 1 (natToUnary 2) k =
        powTwoNat (k + 1) - 1
  | 0 => by
      rfl
  | k + 1 => by
      change
        divisorSigmaPowerFactorNat 1 (natToUnary 2) k +
            natPow (bwordLength (natToUnary 2)) (1 * (k + 1)) =
          powTwoNat ((k + 1) + 1) - 1
      rw [sigmaPowerFactorNat_two_closed k]
      rw [natToUnary_length, Nat.one_mul, natPow_eq_powTwoNat]
      let a := powTwoNat (k + 1)
      calc
        a - 1 + a = a + a - 1 := nat_pred_add_self_comm a (powTwoNat_positive (k + 1))
        _ = 2 * a - 1 := by
              rw [Nat.two_mul]
        _ = powTwoNat ((k + 1) + 1) - 1 := by
              rfl

private theorem profilePowerTwo_valid (k : Nat) (kNonzero : k = 0 -> False) :
    ProfileValid (profilePowerTwo k) := by
  unfold profilePowerTwo
  exact ProfileValid.cons NatPrime_first_pair.left
    kNonzero
    rfl
    ProfileValid.nil

private theorem profileMersenne_valid
    (k : Nat) (prime : MersennePrimeCriterion (k + 1)) :
    ProfileValid (profileMersenne k) := by
  change NatPrime (mersenneHist (k + 1)) at prime
  unfold profileMersenne
  exact ProfileValid.cons prime
    (by intro h; cases h)
    rfl
    ProfileValid.nil

private theorem natToUnary_two_ne_mersenne_succ (k : Nat) :
    natToUnary 2 = mersenneHist (k + 1) -> False := by
  intro same
  have lenEq : 2 = powTwoNat (k + 1) - 1 := by
    have raw := congrArg bwordLength same
    unfold mersenneHist mersenneNat at raw
    rw [natToUnary_length, natToUnary_length] at raw
    exact raw
  have powEqThree : powTwoNat (k + 1) = 3 := by
    calc
      powTwoNat (k + 1) = powTwoNat (k + 1) - 1 + 1 :=
        (nat_pred_add_one (powTwoNat (k + 1))
          (powTwoNat_positive (k + 1))).symm
      _ = 2 + 1 := congrArg (fun x => x + 1) lenEq.symm
      _ = 3 := rfl
  exact powTwoNat_ne_three (k + 1) powEqThree

theorem profileMersenneEven_valid
    (k : Nat) (kNonzero : k = 0 -> False)
    (prime : MersennePrimeCriterion (k + 1)) :
    ProfileValid (profileMersenneEven k) := by
  unfold profileMersenneEven profilePowerTwo profileMersenne
  exact ProfileValid.cons NatPrime_first_pair.left
    kNonzero
    (by
      change (if natToUnary 2 = mersenneHist (k + 1) then true else false) = false
      rw [if_neg (natToUnary_two_ne_mersenne_succ k)])
    (ProfileValid.cons prime
      (by intro h; cases h)
      rfl
      ProfileValid.nil)

private theorem profilePowerTwo_product
    (k : Nat) :
    PrimeFactorizationProduct
      (expandProfile (profilePowerTwo k))
      (natToUnary (powTwoNat k)) := by
  induction k with
  | zero =>
      unfold profilePowerTwo expandProfile expandPrimePower
      exact hsame_refl _
  | succ k ih =>
      unfold profilePowerTwo expandProfile expandPrimePower
      change NatPrime (natToUnary 2) ∧
        ∃ tailProduct : BHist,
          PrimeFactorizationProduct (expandPrimePower (natToUnary 2) k ++ []) tailProduct ∧
            NatMul (natToUnary 2) tailProduct (natToUnary (2 * powTwoNat k))
      exact And.intro NatPrime_first_pair.left
        ⟨natToUnary (powTwoNat k), by
          change
            PrimeFactorizationProduct
              (expandPrimePower (natToUnary 2) k ++ [])
              (natToUnary (powTwoNat k)) at ih
          exact ih,
          natToUnary_mul_rel 2 (powTwoNat k)⟩

private theorem profilePowerTwo_factorization
    (k : Nat) :
    PrimeFactorization (natToUnary (powTwoNat k)) (expandProfile (profilePowerTwo k)) := by
  exact ⟨natToUnary_unary _, profilePowerTwo_product k⟩

private theorem profileMersenne_product
    (k : Nat) (prime : MersennePrimeCriterion (k + 1)) :
    PrimeFactorizationProduct
      (expandProfile (profileMersenne k))
      (mersenneHist (k + 1)) := by
  unfold profileMersenne expandProfile expandPrimePower
  change NatPrime (mersenneHist (k + 1)) ∧
    ∃ tailProduct : BHist,
      PrimeFactorizationProduct [] tailProduct ∧
        NatMul (mersenneHist (k + 1)) tailProduct (mersenneHist (k + 1))
  exact And.intro prime
    ⟨natToUnary 1, hsame_refl _, by
      unfold mersenneHist
      exact natToUnary_mul_one_rel (mersenneNat (k + 1))⟩

private theorem profileMersenne_factorization
    (k : Nat) (prime : MersennePrimeCriterion (k + 1)) :
    PrimeFactorization (mersenneHist (k + 1)) (expandProfile (profileMersenne k)) := by
  exact ⟨natToUnary_unary _, profileMersenne_product k prime⟩

theorem profileMersenneEven_value
    (k : Nat) :
    profileValueNat (profileMersenneEven k) = evenPerfectCandidateNat k := by
  unfold profileMersenneEven evenPerfectCandidateNat
  rw [profileValueNat_append]
  unfold profilePowerTwo profileMersenne profileValueNat mersenneHist mersenneNat
  rw [natToUnary_length, natToUnary_length]
  rw [natPow_eq_powTwoNat]
  rw [natPow_one]
  change powTwoNat k * 1 * ((powTwoNat (k + 1) - 1) * 1) =
    powTwoNat k * (powTwoNat (k + 1) - 1)
  rw [Nat.mul_one, Nat.mul_one]

theorem profileMersenneEven_sigma
    (k : Nat) :
    sigmaNat (profileMersenneEven k) =
      2 * evenPerfectCandidateNat k := by
  unfold profileMersenneEven evenPerfectCandidateNat
  rw [sigmaNat_append]
  unfold profilePowerTwo profileMersenne sigmaNat mersenneHist mersenneNat
  change
    divisorSigmaPowerFactorNat 1 (natToUnary 2) k * 1 *
        ((1 + natPow (bwordLength (natToUnary (powTwoNat (k + 1) - 1))) (1 * 1)) * 1) =
      2 * (powTwoNat k * (powTwoNat (k + 1) - 1))
  rw [sigmaPowerFactorNat_two_closed]
  rw [natToUnary_length, Nat.one_mul]
  rw [natPow_one]
  change
    (powTwoNat (k + 1) - 1) * 1 *
        ((1 + (powTwoNat (k + 1) - 1)) * 1) =
      2 * (powTwoNat k * (powTwoNat (k + 1) - 1))
  rw [Nat.mul_one, Nat.mul_one]
  rw [show 1 + (powTwoNat (k + 1) - 1) = powTwoNat (k + 1) by
    rw [Nat.add_comm]
    exact nat_pred_add_one (powTwoNat (k + 1)) (powTwoNat_positive (k + 1))]
  rw [show powTwoNat (k + 1) = 2 * powTwoNat k by rfl]
  calc
    (powTwoNat (k + 1) - 1) * (2 * powTwoNat k)
        = (2 * powTwoNat k) * (powTwoNat (k + 1) - 1) := by
            rw [Nat.mul_comm]
    _ = 2 * (powTwoNat k * (powTwoNat (k + 1) - 1)) :=
            nat_mul_assoc_pure 2 (powTwoNat k) (powTwoNat (k + 1) - 1)

theorem profileMersenneEven_perfect
    (k : Nat) :
    IsPerfectProfile (profileMersenneEven k) := by
  unfold IsPerfectProfile
  rw [profileMersenneEven_sigma, profileMersenneEven_value]

theorem profileMersenneEven_factorization
    (k : Nat) (prime : MersennePrimeCriterion (k + 1)) :
    PrimeFactorization
      (evenPerfectCandidate k)
      (expandProfile (profileMersenneEven k)) := by
  have leftFactor := profilePowerTwo_factorization k
  have rightFactor := profileMersenne_factorization k prime
  have product :
      PrimeFactorizationProduct (expandProfile (profileMersenneEven k))
        (evenPerfectCandidate k) := by
    unfold profileMersenneEven evenPerfectCandidate evenPerfectCandidateNat
    exact PrimeFactorizationProduct_profile_append_mul
      leftFactor.right
      rightFactor.right
      (natToUnary_mul_rel (powTwoNat k) (mersenneNat (k + 1)))
  exact ⟨natToUnary_unary _, product⟩

theorem euclid_mersenne_even_candidate_perfect_number
    (k : Nat) (kNonzero : k = 0 -> False)
    (prime : MersennePrimeCriterion (k + 1)) :
    PerfectNumber (evenPerfectCandidate k) := by
  exact ⟨profileMersenneEven k,
    profileMersenneEven_valid k kNonzero prime,
    (profileMersenneEven_factorization k prime),
    (profileMersenneEven_perfect k)⟩

def NatSix : BHist :=
  natToUnary 6

def NatTwentyEight : BHist :=
  natToUnary 28

def NatFourHundredNinetySix : BHist :=
  natToUnary 496

def listNatSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + listNatSum xs

def NatPerfectBySigmaProfileValue (n : Nat) (profile : PrimePowerProfile) : Prop :=
  profileValueNat profile = n ∧ sigmaNat profile = 2 * n

def divisorsSix : List Nat :=
  [1, 2, 3, 6]

def divisorsTwentyEight : List Nat :=
  [1, 2, 4, 7, 14, 28]

def divisorsFourHundredNinetySix : List Nat :=
  [1, 2, 4, 8, 16, 31, 62, 124, 248, 496]

theorem sigma_six_divisor_list :
    listNatSum divisorsSix = 12 := by
  rfl

theorem sigma_twentyEight_divisor_list :
    listNatSum divisorsTwentyEight = 56 := by
  rfl

theorem sigma_fourHundredNinetySix_divisor_list :
    listNatSum divisorsFourHundredNinetySix = 992 := by
  rfl

theorem six_perfect_by_sigma_profile :
    NatPerfectBySigmaProfileValue 6 (profileMersenneEven 1) := by
  constructor
  · exact profileMersenneEven_value 1
  · exact profileMersenneEven_sigma 1

theorem six_perfect_number_export :
    PerfectNumber NatSix := by
  unfold NatSix
  exact AbundantDeficientUp.perfect_six_number

theorem mersenne_prime_exponent_two :
    MersennePrimeCriterion 2 := by
  unfold MersennePrimeCriterion mersenneHist mersenneNat powTwoNat
  exact NatPrime_first_pair.right

theorem six_from_mersenne_euclid :
    PerfectNumber (evenPerfectCandidate 1) := by
  exact euclid_mersenne_even_candidate_perfect_number 1
    (by intro h; cases h)
    mersenne_prime_exponent_two

theorem evenPerfectCandidate_one_value :
    evenPerfectCandidate 1 = NatSix := by
  rfl

theorem twentyEight_perfect_by_sigma_profile :
    NatPerfectBySigmaProfileValue 28 (profileMersenneEven 2) := by
  constructor
  · exact profileMersenneEven_value 2
  · exact profileMersenneEven_sigma 2

theorem mersenne_prime_exponent_three :
    MersennePrimeCriterion 3 := by
  unfold MersennePrimeCriterion mersenneHist mersenneNat powTwoNat
  change NatPrime (natToUnary 7)
  exact minFactor_prime (BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
    (unary_e1_closed unary_empty)
    (natToUnary_unary 7)
    (by
      rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
      rw [natToUnary_length]
      decide))

theorem twentyEight_from_mersenne_euclid :
    PerfectNumber NatTwentyEight := by
  have raw :
      PerfectNumber (evenPerfectCandidate 2) :=
    euclid_mersenne_even_candidate_perfect_number 2
      (by intro h; cases h)
      mersenne_prime_exponent_three
  exact raw

theorem fourHundredNinetySix_perfect_by_sigma_profile :
    NatPerfectBySigmaProfileValue 496 (profileMersenneEven 4) := by
  constructor
  · exact profileMersenneEven_value 4
  · exact profileMersenneEven_sigma 4

theorem mersenne_prime_exponent_five :
    MersennePrimeCriterion 5 := by
  unfold MersennePrimeCriterion mersenneHist mersenneNat powTwoNat
  change NatPrime (natToUnary 31)
  exact minFactor_prime (BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
    (unary_e1_closed unary_empty)
    (natToUnary_unary 31)
    (by
      rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
      rw [natToUnary_length]
      decide))

theorem fourHundredNinetySix_from_mersenne_euclid :
    PerfectNumber NatFourHundredNinetySix := by
  have raw :
      PerfectNumber (evenPerfectCandidate 4) :=
    euclid_mersenne_even_candidate_perfect_number 4
      (by intro h; cases h)
      mersenne_prime_exponent_five
  exact raw

theorem PerfectNumberUp_export :
    PerfectNumber NatSix ∧ PerfectNumber NatTwentyEight ∧
      PerfectNumber NatFourHundredNinetySix ∧
        NatPerfectBySigmaProfileValue 6 (profileMersenneEven 1) ∧
          NatPerfectBySigmaProfileValue 28 (profileMersenneEven 2) ∧
            NatPerfectBySigmaProfileValue 496 (profileMersenneEven 4) := by
  exact ⟨six_perfect_number_export,
    twentyEight_from_mersenne_euclid,
    fourHundredNinetySix_from_mersenne_euclid,
    six_perfect_by_sigma_profile,
    twentyEight_perfect_by_sigma_profile,
    fourHundredNinetySix_perfect_by_sigma_profile⟩

end BEDC.Derived.PerfectNumberUp
