import BEDC.Derived.AliquotSequenceUp

set_option maxRecDepth 3000

namespace BEDC.Derived.AmicableNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.PrimeUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.AbundantDeficientUp
open BEDC.Derived.AliquotSequenceUp

private abbrev NatOne : BHist := BHist.e1 BHist.Empty

def NatTwo : BHist := natToUnary 2
def NatFive : BHist := natToUnary 5
def NatEleven : BHist := natToUnary 11
def NatSeventyOne : BHist := natToUnary 71
def NatTwoHundredTwenty : BHist := natToUnary 220
def NatTwoHundredEightyFour : BHist := natToUnary 284

private abbrev NatFiftyFive : BHist := natToUnary 55
private abbrev NatOneHundredTen : BHist := natToUnary 110
private abbrev NatOneHundredFortyTwo : BHist := natToUnary 142

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k ->
      hsame h k := by
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

private theorem natSubEqIffEqAddOfLe (a b c : Nat) :
    a ≤ c -> (c - a = b ↔ c = a + b) := by
  intro le
  constructor
  · intro subEq
    have cancel : (c - a) + a = c := natSubAddCancelOfLe a c le
    calc
      c = (c - a) + a := cancel.symm
      _ = b + a := by rw [subEq]
      _ = a + b := Nat.add_comm b a
  · intro sumEq
    rw [sumEq]
    exact natAddSubCancelLeft a b

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

theorem NatTwo_prime : NatPrime NatTwo := by
  unfold NatTwo
  exact NatPrime_first_pair.left

theorem NatFive_prime : NatPrime NatFive := by
  have large : NatUnaryStrictPrefix NatOne NatFive := by
    unfold NatFive
    exact natOne_strict_natToUnary_succ_succ 3
  unfold NatFive
  change NatPrime (minFactor (natToUnary 5) large)
  exact minFactor_prime large

theorem NatEleven_prime : NatPrime NatEleven := by
  have large : NatUnaryStrictPrefix NatOne NatEleven := by
    unfold NatEleven
    exact natOne_strict_natToUnary_succ_succ 9
  unfold NatEleven
  change NatPrime (minFactor (natToUnary 11) large)
  exact minFactor_prime large

theorem NatSeventyOne_prime : NatPrime NatSeventyOne := by
  have large : NatUnaryStrictPrefix NatOne NatSeventyOne := by
    unfold NatSeventyOne
    exact natOne_strict_natToUnary_succ_succ 69
  unfold NatSeventyOne
  change NatPrime (minFactor (natToUnary 71) large)
  exact minFactor_prime large

def profileTwoHundredTwenty : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 2 },
    { prime := NatFive, exponent := 1 },
    { prime := NatEleven, exponent := 1 }]

def profileTwoHundredEightyFour : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 2 },
    { prime := NatSeventyOne, exponent := 1 }]

theorem profileTwoHundredTwenty_valid : ProfileValid profileTwoHundredTwenty := by
  unfold profileTwoHundredTwenty
  exact ProfileValid.cons NatTwo_prime
    (by intro h; cases h)
    rfl
    (ProfileValid.cons NatFive_prime
      (by intro h; cases h)
      rfl
      (ProfileValid.cons NatEleven_prime
        (by intro h; cases h)
        rfl
        ProfileValid.nil))

theorem profileTwoHundredEightyFour_valid :
    ProfileValid profileTwoHundredEightyFour := by
  unfold profileTwoHundredEightyFour
  exact ProfileValid.cons NatTwo_prime
    (by intro h; cases h)
    rfl
    (ProfileValid.cons NatSeventyOne_prime
      (by intro h; cases h)
      rfl
      ProfileValid.nil)

private theorem primeFactorizationProduct_singleton
    {p : BHist} (pPrime : NatPrime p) :
    PrimeFactorizationProduct [p] p := by
  exact ⟨pPrime, NatOne, hsame_refl NatOne,
    NatMul.succ (NatMul.zero pPrime.left) (cont_left_unit p)⟩

private theorem primeFactorizationProduct_five_eleven :
    PrimeFactorizationProduct [NatFive, NatEleven] NatFiftyFive := by
  unfold NatFiftyFive
  exact ⟨NatFive_prime, NatEleven,
    primeFactorizationProduct_singleton NatEleven_prime,
    natToUnary_mul_rel 5 11⟩

private theorem primeFactorizationProduct_two_five_eleven :
    PrimeFactorizationProduct [NatTwo, NatFive, NatEleven] NatOneHundredTen := by
  unfold NatOneHundredTen
  exact ⟨NatTwo_prime, NatFiftyFive,
    primeFactorizationProduct_five_eleven,
    natToUnary_mul_rel 2 55⟩

private theorem primeFactorizationProduct_two_two_five_eleven :
    PrimeFactorizationProduct [NatTwo, NatTwo, NatFive, NatEleven]
      NatTwoHundredTwenty := by
  unfold NatTwoHundredTwenty
  exact ⟨NatTwo_prime, NatOneHundredTen,
    primeFactorizationProduct_two_five_eleven,
    natToUnary_mul_rel 2 110⟩

private theorem primeFactorizationProduct_two_seventyOne :
    PrimeFactorizationProduct [NatTwo, NatSeventyOne] NatOneHundredFortyTwo := by
  unfold NatOneHundredFortyTwo
  exact ⟨NatTwo_prime, NatSeventyOne,
    primeFactorizationProduct_singleton NatSeventyOne_prime,
    natToUnary_mul_rel 2 71⟩

private theorem primeFactorizationProduct_two_two_seventyOne :
    PrimeFactorizationProduct [NatTwo, NatTwo, NatSeventyOne]
      NatTwoHundredEightyFour := by
  unfold NatTwoHundredEightyFour
  exact ⟨NatTwo_prime, NatOneHundredFortyTwo,
    primeFactorizationProduct_two_seventyOne,
    natToUnary_mul_rel 2 142⟩

theorem NatTwoHundredTwenty_factorization :
    PrimeFactorization NatTwoHundredTwenty (expandProfile profileTwoHundredTwenty) := by
  constructor
  · unfold NatTwoHundredTwenty
    exact natToUnary_unary 220
  · unfold profileTwoHundredTwenty expandProfile expandPrimePower
    exact primeFactorizationProduct_two_two_five_eleven

theorem NatTwoHundredEightyFour_factorization :
    PrimeFactorization NatTwoHundredEightyFour
      (expandProfile profileTwoHundredEightyFour) := by
  constructor
  · unfold NatTwoHundredEightyFour
    exact natToUnary_unary 284
  · unfold profileTwoHundredEightyFour expandProfile expandPrimePower
    exact primeFactorizationProduct_two_two_seventyOne

theorem profileTwoHundredTwenty_value :
    profileValueNat profileTwoHundredTwenty = 220 := by
  rfl

theorem profileTwoHundredEightyFour_value :
    profileValueNat profileTwoHundredEightyFour = 284 := by
  rfl

theorem sigmaTwoHundredTwenty_value :
    sigmaNat profileTwoHundredTwenty = 504 := by
  rfl

theorem sigmaTwoHundredEightyFour_value :
    sigmaNat profileTwoHundredEightyFour = 504 := by
  rfl

theorem aliquotTwoHundredTwenty_value :
    aliquotSumNat profileTwoHundredTwenty = 284 := by
  rfl

theorem aliquotTwoHundredEightyFour_value :
    aliquotSumNat profileTwoHundredEightyFour = 220 := by
  rfl

def AmicablePairProfile (left right : PrimePowerProfile) : Prop :=
  aliquotSumNat left = profileValueNat right ∧
    aliquotSumNat right = profileValueNat left ∧
      profileValueNat left ≠ profileValueNat right

def SigmaCommonSumProfile (left right : PrimePowerProfile) : Prop :=
  sigmaNat left = profileValueNat left + profileValueNat right ∧
    sigmaNat right = profileValueNat left + profileValueNat right ∧
      profileValueNat left ≠ profileValueNat right

def AmicablePairOfProfiles
    (a b : BHist) (left right : PrimePowerProfile) : Prop :=
  AliquotSumOfProfile a b left ∧
    AliquotSumOfProfile b a right ∧
      (hsame a b -> False)

def AmicablePair (a b : BHist) : Prop :=
  ∃ left right : PrimePowerProfile, AmicablePairOfProfiles a b left right

def SelfAmicableBoundaryProfile (profile : PrimePowerProfile) : Prop :=
  aliquotSumNat profile = profileValueNat profile

def SelfAmicableBoundary (n : BHist) : Prop :=
  AliquotFixedNumber n

theorem aliquotSumNat_eq_value_iff_sigmaNat_eq_sum
    (left right : PrimePowerProfile) :
    aliquotSumNat left = profileValueNat right ↔
      sigmaNat left = profileValueNat left + profileValueNat right := by
  unfold aliquotSumNat properDivisorSumNat
  exact natSubEqIffEqAddOfLe (profileValueNat left) (profileValueNat right)
    (sigmaNat left) (profileValueNat_le_sigmaNat left)

theorem amicablePairProfile_iff_sigma_eq_sum
    (left right : PrimePowerProfile) :
    AmicablePairProfile left right ↔ SigmaCommonSumProfile left right := by
  unfold AmicablePairProfile SigmaCommonSumProfile
  constructor
  · intro amicable
    have leftSigma :
        sigmaNat left = profileValueNat left + profileValueNat right :=
      (aliquotSumNat_eq_value_iff_sigmaNat_eq_sum left right).mp
        amicable.left
    have rightSigmaRaw :
        sigmaNat right = profileValueNat right + profileValueNat left :=
      (aliquotSumNat_eq_value_iff_sigmaNat_eq_sum right left).mp
        amicable.right.left
    have rightSigma :
        sigmaNat right = profileValueNat left + profileValueNat right := by
      rw [Nat.add_comm]
      exact rightSigmaRaw
    exact ⟨leftSigma, rightSigma, amicable.right.right⟩
  · intro sigmaData
    have leftAliquot :
        aliquotSumNat left = profileValueNat right :=
      (aliquotSumNat_eq_value_iff_sigmaNat_eq_sum left right).mpr
        sigmaData.left
    have rightSigmaRaw :
        sigmaNat right = profileValueNat right + profileValueNat left := by
      rw [Nat.add_comm]
      exact sigmaData.right.left
    have rightAliquot :
        aliquotSumNat right = profileValueNat left :=
      (aliquotSumNat_eq_value_iff_sigmaNat_eq_sum right left).mpr
        rightSigmaRaw
    exact ⟨leftAliquot, rightAliquot, sigmaData.right.right⟩

private theorem profile_value_hsame_absurd
    {a b : BHist} {left right : PrimePowerProfile} :
    PrimeFactorization a (expandProfile left) ->
      PrimeFactorization b (expandProfile right) ->
        profileValueNat left ≠ profileValueNat right ->
          hsame a b -> False := by
  intro factorLeft factorRight valueNe sameAB
  have sameLeftA :
      hsame (natToUnary (profileValueNat left)) a :=
    natToUnary_profileValue_hsame_of_factorization factorLeft
  have sameRightB :
      hsame (natToUnary (profileValueNat right)) b :=
    natToUnary_profileValue_hsame_of_factorization factorRight
  have sameValues :
      hsame (natToUnary (profileValueNat left))
        (natToUnary (profileValueNat right)) :=
    hsame_trans sameLeftA (hsame_trans sameAB (hsame_symm sameRightB))
  have lengthEq := congrArg bwordLength sameValues
  rw [natToUnary_length, natToUnary_length] at lengthEq
  exact valueNe lengthEq

private theorem profile_value_eq_of_aliquot_hsame
    {target : BHist} {sourceProfile targetProfile : PrimePowerProfile} :
    PrimeFactorization target (expandProfile targetProfile) ->
      hsame target (aliquotSum sourceProfile) ->
        aliquotSumNat sourceProfile = profileValueNat targetProfile := by
  intro targetFactor sameTargetAliquot
  have sameValueTarget :
      hsame (natToUnary (profileValueNat targetProfile)) target :=
    natToUnary_profileValue_hsame_of_factorization targetFactor
  have sameValueAliquot :
      hsame (natToUnary (profileValueNat targetProfile))
        (aliquotSum sourceProfile) :=
    hsame_trans sameValueTarget sameTargetAliquot
  have lengthEq := congrArg bwordLength sameValueAliquot
  unfold aliquotSum at lengthEq
  rw [natToUnary_length, natToUnary_length] at lengthEq
  exact lengthEq.symm

private theorem aliquot_hsame_of_profile_value_eq
    {target : BHist} {sourceProfile targetProfile : PrimePowerProfile} :
    PrimeFactorization target (expandProfile targetProfile) ->
      aliquotSumNat sourceProfile = profileValueNat targetProfile ->
        hsame target (aliquotSum sourceProfile) := by
  intro targetFactor eqValue
  have sameTargetValue :
      hsame target (natToUnary (profileValueNat targetProfile)) :=
    hsame_symm (natToUnary_profileValue_hsame_of_factorization targetFactor)
  have sameValueAliquot :
      hsame (natToUnary (profileValueNat targetProfile))
        (aliquotSum sourceProfile) := by
    apply unary_hsame_of_length
    · exact natToUnary_unary _
    · exact aliquotSum_unary sourceProfile
    · unfold aliquotSum
      rw [natToUnary_length, natToUnary_length]
      exact eqValue.symm
  exact hsame_trans sameTargetValue sameValueAliquot

private theorem natToUnary_prefix_gap_absurd :
    ∀ n k : Nat, hsame (natToUnary n) (natToUnary (n + Nat.succ k)) -> False
  | 0, k, same => by
      rw [Nat.zero_add] at same
      change hsame BHist.Empty (BHist.e1 (natToUnary k)) at same
      exact not_hsame_emp_e1 same
  | Nat.succ n, k, same => by
      rw [Nat.succ_add] at same
      change hsame (BHist.e1 (natToUnary n))
        (BHist.e1 (natToUnary (n + Nat.succ k))) at same
      exact natToUnary_prefix_gap_absurd n k (hsame_e1_iff.mp same)

theorem amicablePairOfProfiles_iff_amicablePairProfile
    (a b : BHist) (left right : PrimePowerProfile) :
    AmicablePairOfProfiles a b left right ↔
      ProfileValid left ∧ PrimeFactorization a (expandProfile left) ∧
        ProfileValid right ∧ PrimeFactorization b (expandProfile right) ∧
          AmicablePairProfile left right := by
  constructor
  · intro pair
    have leftData := pair.left
    have rightData := pair.right.left
    have leftAliquot :
        aliquotSumNat left = profileValueNat right :=
      profile_value_eq_of_aliquot_hsame rightData.right.left leftData.right.right
    have rightAliquot :
        aliquotSumNat right = profileValueNat left :=
      profile_value_eq_of_aliquot_hsame leftData.right.left rightData.right.right
    have valueNe : profileValueNat left ≠ profileValueNat right := by
      intro valueEq
      have sameLeftA :
          hsame (natToUnary (profileValueNat left)) a :=
        natToUnary_profileValue_hsame_of_factorization leftData.right.left
      have sameRightB :
          hsame (natToUnary (profileValueNat right)) b :=
        natToUnary_profileValue_hsame_of_factorization rightData.right.left
      have sameValueB :
          hsame (natToUnary (profileValueNat left)) b := by
        rw [valueEq]
        exact sameRightB
      exact pair.right.right (hsame_trans (hsame_symm sameLeftA) sameValueB)
    exact ⟨leftData.left, leftData.right.left, rightData.left, rightData.right.left,
      leftAliquot, rightAliquot, valueNe⟩
  · intro data
    have leftValid := data.left
    have leftFactor := data.right.left
    have rightValid := data.right.right.left
    have rightFactor := data.right.right.right.left
    have profilePair := data.right.right.right.right
    have leftAliquot :
        AliquotSumOfProfile a b left :=
      ⟨leftValid, leftFactor,
        aliquot_hsame_of_profile_value_eq rightFactor profilePair.left⟩
    have rightAliquot :
        AliquotSumOfProfile b a right :=
      ⟨rightValid, rightFactor,
        aliquot_hsame_of_profile_value_eq leftFactor profilePair.right.left⟩
    have distinct :
        hsame a b -> False :=
      profile_value_hsame_absurd leftFactor rightFactor profilePair.right.right
    exact ⟨leftAliquot, rightAliquot, distinct⟩

theorem amicablePairOfProfiles_iff_sigma_eq_sum
    (a b : BHist) (left right : PrimePowerProfile) :
    AmicablePairOfProfiles a b left right ↔
      ProfileValid left ∧ PrimeFactorization a (expandProfile left) ∧
        ProfileValid right ∧ PrimeFactorization b (expandProfile right) ∧
          SigmaCommonSumProfile left right := by
  constructor
  · intro pair
    have data :=
      (amicablePairOfProfiles_iff_amicablePairProfile a b left right).mp pair
    exact ⟨data.left, data.right.left, data.right.right.left,
      data.right.right.right.left,
      (amicablePairProfile_iff_sigma_eq_sum left right).mp
        data.right.right.right.right⟩
  · intro data
    exact (amicablePairOfProfiles_iff_amicablePairProfile a b left right).mpr
      ⟨data.left, data.right.left, data.right.right.left,
        data.right.right.right.left,
        (amicablePairProfile_iff_sigma_eq_sum left right).mpr
          data.right.right.right.right⟩

theorem profileTwoHundredTwenty_profileTwoHundredEightyFour_amicableProfile :
    AmicablePairProfile profileTwoHundredTwenty profileTwoHundredEightyFour := by
  unfold AmicablePairProfile
  exact ⟨aliquotTwoHundredTwenty_value,
    aliquotTwoHundredEightyFour_value,
    by
      intro valueEq
      exact natToUnary_prefix_gap_absurd 220 63 (unary_hsame_of_length
        (natToUnary_unary 220) (natToUnary_unary 284) valueEq)⟩

theorem profileTwoHundredTwenty_profileTwoHundredEightyFour_sigmaCommonSum :
    SigmaCommonSumProfile profileTwoHundredTwenty profileTwoHundredEightyFour := by
  exact (amicablePairProfile_iff_sigma_eq_sum
    profileTwoHundredTwenty profileTwoHundredEightyFour).mp
      profileTwoHundredTwenty_profileTwoHundredEightyFour_amicableProfile

theorem NatTwoHundredTwenty_aliquot_to_NatTwoHundredEightyFour :
    AliquotSumOfProfile NatTwoHundredTwenty NatTwoHundredEightyFour
      profileTwoHundredTwenty := by
  exact ⟨profileTwoHundredTwenty_valid, NatTwoHundredTwenty_factorization,
    aliquot_hsame_of_profile_value_eq NatTwoHundredEightyFour_factorization
      aliquotTwoHundredTwenty_value⟩

theorem NatTwoHundredEightyFour_aliquot_to_NatTwoHundredTwenty :
    AliquotSumOfProfile NatTwoHundredEightyFour NatTwoHundredTwenty
      profileTwoHundredEightyFour := by
  exact ⟨profileTwoHundredEightyFour_valid,
    NatTwoHundredEightyFour_factorization,
    aliquot_hsame_of_profile_value_eq NatTwoHundredTwenty_factorization
      aliquotTwoHundredEightyFour_value⟩

theorem NatTwoHundredTwenty_ne_NatTwoHundredEightyFour :
    hsame NatTwoHundredTwenty NatTwoHundredEightyFour -> False := by
  intro same
  unfold NatTwoHundredTwenty NatTwoHundredEightyFour at same
  exact natToUnary_prefix_gap_absurd 220 63 same

theorem NatTwoHundredTwenty_NatTwoHundredEightyFour_amicableOfProfiles :
    AmicablePairOfProfiles NatTwoHundredTwenty NatTwoHundredEightyFour
      profileTwoHundredTwenty profileTwoHundredEightyFour := by
  exact ⟨NatTwoHundredTwenty_aliquot_to_NatTwoHundredEightyFour,
    NatTwoHundredEightyFour_aliquot_to_NatTwoHundredTwenty,
    NatTwoHundredTwenty_ne_NatTwoHundredEightyFour⟩

theorem NatTwoHundredTwenty_NatTwoHundredEightyFour_amicable :
    AmicablePair NatTwoHundredTwenty NatTwoHundredEightyFour := by
  exact ⟨profileTwoHundredTwenty, profileTwoHundredEightyFour,
    NatTwoHundredTwenty_NatTwoHundredEightyFour_amicableOfProfiles⟩

theorem NatTwoHundredTwenty_NatTwoHundredEightyFour_sigma_characterization :
    SigmaCommonSumProfile profileTwoHundredTwenty profileTwoHundredEightyFour := by
  exact profileTwoHundredTwenty_profileTwoHundredEightyFour_sigmaCommonSum

theorem perfectProfile_iff_self_amicable_boundary
    (profile : PrimePowerProfile) :
    IsPerfectProfile profile ↔ SelfAmicableBoundaryProfile profile := by
  unfold SelfAmicableBoundaryProfile
  exact perfectProfile_iff_aliquotPerfectProfile profile

theorem perfectNumber_iff_self_amicable_boundary (n : BHist) :
    PerfectNumber n ↔ SelfAmicableBoundary n := by
  unfold SelfAmicableBoundary
  exact perfectNumber_iff_aliquotSum_eq_self n

end BEDC.Derived.AmicableNumberUp
