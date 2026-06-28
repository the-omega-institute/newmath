import BEDC.Derived.AliquotSequenceUp

namespace BEDC.Derived.SuperperfectUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.PrimeUp
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.AbundantDeficientUp

def SuperperfectProfile
    (profile sigmaProfile : PrimePowerProfile) : Prop :=
  ProfileValid profile ∧ ProfileValid sigmaProfile ∧
    profileValueNat sigmaProfile = sigmaNat profile ∧
      sigmaNat sigmaProfile = 2 * profileValueNat profile

def MultiplyPerfectProfile
    (k : Nat) (profile : PrimePowerProfile) : Prop :=
  sigmaNat profile = k * profileValueNat profile

def SuperperfectNumber (n : BHist) : Prop :=
  ∃ profile sigmaProfile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      SuperperfectProfile profile sigmaProfile

def MultiplyPerfectNumber (k : Nat) (n : BHist) : Prop :=
  ∃ profile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      MultiplyPerfectProfile k profile

def NatOne : BHist := natToUnary 1
def NatTwo : BHist := natToUnary 2
def NatThree : BHist := natToUnary 3
def NatFour : BHist := natToUnary 4
def NatSeven : BHist := natToUnary 7

def profileTwo : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 1 }]

def profileFour : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 2 }]

def profileSeven : PrimePowerProfile :=
  [{ prime := NatSeven, exponent := 1 }]

def profilePowerTwo (k : Nat) : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := k }]

def profileMersennePrime (p : BHist) : PrimePowerProfile :=
  [{ prime := p, exponent := 1 }]

def evenSuperperfectCandidateNat (k : Nat) : Nat :=
  natPow 2 k

theorem natOne_unary : UnaryHistory NatOne := by
  unfold NatOne
  exact natToUnary_unary 1

theorem natTwo_unary : UnaryHistory NatTwo := by
  unfold NatTwo
  exact natToUnary_unary 2

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

theorem natTwo_prime : NatPrime NatTwo := by
  unfold NatTwo
  exact NatPrime_first_pair.left

theorem natSeven_prime : NatPrime NatSeven := by
  have large : NatUnaryStrictPrefix NatOne NatSeven := by
    unfold NatSeven
    exact natOne_strict_natToUnary_succ_succ 5
  unfold NatSeven
  change NatPrime (minFactor (natToUnary 7) large)
  exact minFactor_prime large

theorem profileTwo_valid : ProfileValid profileTwo := by
  unfold profileTwo
  exact ProfileValid.cons natTwo_prime
    (by intro h; cases h)
    rfl
    ProfileValid.nil

theorem profileFour_valid : ProfileValid profileFour := by
  unfold profileFour
  exact ProfileValid.cons natTwo_prime
    (by intro h; cases h)
    rfl
    ProfileValid.nil

theorem profileSeven_valid : ProfileValid profileSeven := by
  unfold profileSeven
  exact ProfileValid.cons natSeven_prime
    (by intro h; cases h)
    rfl
    ProfileValid.nil

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        (NatUp_unary_standard_bridge.right.right.right.left
          resultData.left (natToUnary_unary _)).mpr
          ((NatMul_bwordLength resultData.right).trans (by
            rw [natToUnary_length, natToUnary_length, natToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem profileTwo_factorization :
    PrimeFactorization NatTwo (expandProfile profileTwo) := by
  unfold profileTwo expandProfile expandPrimePower NatTwo
  change PrimeFactorization (natToUnary 2) [natToUnary 2]
  constructor
  · exact natToUnary_unary 2
  · change NatPrime (natToUnary 2) ∧
      ∃ tailProduct : BHist,
        PrimeFactorizationProduct [] tailProduct ∧
          NatMul (natToUnary 2) tailProduct (natToUnary 2)
    exact And.intro NatPrime_first_pair.left
      ⟨natToUnary 1, rfl, by simpa using natToUnary_mul_rel 2 1⟩

theorem profileFour_factorization :
    PrimeFactorization NatFour (expandProfile profileFour) := by
  unfold profileFour expandProfile expandPrimePower NatFour NatTwo
  change PrimeFactorization (natToUnary 4) [natToUnary 2, natToUnary 2]
  constructor
  · exact natToUnary_unary 4
  · change NatPrime (natToUnary 2) ∧
      ∃ tailProduct : BHist,
        PrimeFactorizationProduct [natToUnary 2] tailProduct ∧
          NatMul (natToUnary 2) tailProduct (natToUnary 4)
    exact And.intro NatPrime_first_pair.left
      ⟨natToUnary 2, profileTwo_factorization.right,
        by simpa using natToUnary_mul_rel 2 2⟩

theorem profileTwo_value : profileValueNat profileTwo = 2 := by
  rfl

theorem profileFour_value : profileValueNat profileFour = 4 := by
  rfl

theorem profileSeven_value : profileValueNat profileSeven = 7 := by
  rfl

theorem sigmaTwo_value : sigmaNat profileTwo = 3 := by
  rfl

theorem sigmaFour_value : sigmaNat profileFour = 7 := by
  rfl

theorem sigmaSeven_value : sigmaNat profileSeven = 8 := by
  rfl

theorem multiplyPerfectProfile_two_iff_perfectProfile
    (profile : PrimePowerProfile) :
    MultiplyPerfectProfile 2 profile ↔ IsPerfectProfile profile := by
  rfl

theorem twoPerfectNumber_iff_perfectNumber (n : BHist) :
    MultiplyPerfectNumber 2 n ↔ PerfectNumber n := by
  constructor
  · intro data
    cases data with
    | intro profile profileData =>
        exact ⟨profile, profileData.left, profileData.right.left,
          profileData.right.right⟩
  · intro data
    cases data with
    | intro profile profileData =>
        exact ⟨profile, profileData.left, profileData.right.left,
          profileData.right.right⟩

theorem profileTwo_superperfect :
    SuperperfectProfile profileTwo profileThree := by
  exact ⟨profileTwo_valid, profileThree_valid, sigmaTwo_value,
    by
      unfold sigmaNat profileThree profileTwo profileValueNat
      rfl⟩

theorem profileFour_superperfect :
    SuperperfectProfile profileFour profileSeven := by
  exact ⟨profileFour_valid, profileSeven_valid, sigmaFour_value,
    by
      unfold sigmaNat profileSeven profileFour profileValueNat
      rfl⟩

theorem two_superperfect_number : SuperperfectNumber NatTwo := by
  exact ⟨profileTwo, profileThree, profileTwo_valid,
    profileTwo_factorization, profileTwo_superperfect⟩

theorem four_superperfect_number : SuperperfectNumber NatFour := by
  exact ⟨profileFour, profileSeven, profileFour_valid,
    profileFour_factorization, profileFour_superperfect⟩

private theorem natPow_two_pos (n : Nat) :
    0 < natPow 2 n := by
  induction n with
  | zero =>
      exact Nat.zero_lt_succ 0
  | succ n ih =>
      change 0 < 2 * natPow 2 n
      exact Nat.mul_pos (by decide) ih

private theorem natPow_one (base : Nat) :
    natPow base 1 = base := by
  change base * 1 = base
  rw [Nat.mul_one]

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

private theorem nat_pred_add_one (a : Nat) :
    0 < a -> a - 1 + 1 = a := by
  intro pos
  cases a with
  | zero =>
      cases pos
  | succ n =>
      rfl

private theorem sigmaPowerFactorNat_two_closed :
    ∀ k : Nat,
      divisorSigmaPowerFactorNat 1 NatTwo k =
        natPow 2 (k + 1) - 1
  | 0 => by
      rfl
  | k + 1 => by
      change
        divisorSigmaPowerFactorNat 1 NatTwo k +
            natPow (bwordLength NatTwo) (1 * (k + 1)) =
          natPow 2 ((k + 1) + 1) - 1
      rw [sigmaPowerFactorNat_two_closed k]
      unfold NatTwo
      rw [natToUnary_length, Nat.one_mul]
      let a := natPow 2 (k + 1)
      have oneLe : 1 ≤ a := Nat.succ_le_of_lt (natPow_two_pos (k + 1))
      calc
        natPow 2 (k + 1) - 1 + natPow 2 (k + 1)
            = natPow 2 (k + 1) + natPow 2 (k + 1) - 1 := by
                exact nat_pred_add_self_comm (natPow 2 (k + 1))
                  (natPow_two_pos (k + 1))
        _ = 2 * natPow 2 (k + 1) - 1 := by
                rw [Nat.two_mul]
        _ = natPow 2 ((k + 1) + 1) - 1 := by
                rfl

theorem profileMersenneEven_superperfect
    (k : Nat) (p : BHist)
    (kNonzero : k = 0 -> False)
    (pPrime : NatPrime p)
    (pLength : bwordLength p = natPow 2 (k + 1) - 1) :
    SuperperfectProfile
      (profilePowerTwo k)
      (profileMersennePrime p) := by
  have mainValid : ProfileValid (profilePowerTwo k) := by
    unfold profilePowerTwo
    exact ProfileValid.cons natTwo_prime
      kNonzero
      rfl
      ProfileValid.nil
  have sigmaValid :
      ProfileValid (profileMersennePrime p) := by
    unfold profileMersennePrime
    exact ProfileValid.cons pPrime
      (by intro h; cases h)
      rfl
      ProfileValid.nil
  constructor
  · exact mainValid
  · constructor
    · exact sigmaValid
    · constructor
      · unfold profileMersennePrime profilePowerTwo profileValueNat sigmaNat
        change
          natPow (bwordLength p) 1 * 1 =
            divisorSigmaPowerFactorNat 1 NatTwo k * 1
        rw [pLength, sigmaPowerFactorNat_two_closed k]
        rw [natPow_one]
      · unfold profileMersennePrime profilePowerTwo profileValueNat sigmaNat
        unfold divisorSigmaProfileNat divisorSigmaPowerFactorNat
        rw [pLength]
        calc
          (1 + natPow (natPow 2 (k + 1) - 1) (1 * 1)) * 1 =
              1 + (natPow 2 (k + 1) - 1) := by
                rw [Nat.mul_one, natPow_one]
          _ =
              natPow 2 (k + 1) := by
                rw [Nat.add_comm, nat_pred_add_one (natPow 2 (k + 1))
                  (natPow_two_pos (k + 1))]
          _ = 2 * (natPow (bwordLength NatTwo) k * 1) := by
                unfold NatTwo
                rw [natToUnary_length, Nat.mul_one]
                rfl

theorem evenSuperperfectCandidateNat_eq_profile_value
    (k : Nat) :
    profileValueNat (profilePowerTwo k) =
      evenSuperperfectCandidateNat k := by
  unfold profilePowerTwo profileValueNat evenSuperperfectCandidateNat NatTwo
  rw [natToUnary_length]
  exact Nat.mul_one (natPow 2 k)

theorem SuperperfectUp_constructive_export :
    SuperperfectProfile profileTwo profileThree ∧
      SuperperfectProfile profileFour profileSeven ∧
        SuperperfectNumber NatTwo ∧
          SuperperfectNumber NatFour ∧
            (∀ profile : PrimePowerProfile,
              MultiplyPerfectProfile 2 profile ↔ IsPerfectProfile profile) := by
  exact ⟨profileTwo_superperfect,
    profileFour_superperfect,
    two_superperfect_number,
    four_superperfect_number,
    multiplyPerfectProfile_two_iff_perfectProfile⟩

end BEDC.Derived.SuperperfectUp
