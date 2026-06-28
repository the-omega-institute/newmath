import BEDC.Derived.AbundantDeficientUp

namespace BEDC.Derived.AliquotSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.AbundantDeficientUp

def aliquotSumNat (profile : PrimePowerProfile) : Nat :=
  properDivisorSumNat profile

def aliquotSum (profile : PrimePowerProfile) : BHist :=
  natToUnary (aliquotSumNat profile)

def AliquotSumOfProfile (n s : BHist) (profile : PrimePowerProfile) : Prop :=
  ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
    hsame s (aliquotSum profile)

def AliquotSumNumber (n s : BHist) : Prop :=
  ∃ profile : PrimePowerProfile, AliquotSumOfProfile n s profile

def AliquotFixedNumber (n : BHist) : Prop :=
  AliquotSumNumber n n

def AliquotAbundantProfile (profile : PrimePowerProfile) : Prop :=
  profileValueNat profile < aliquotSumNat profile

def AliquotDeficientProfile (profile : PrimePowerProfile) : Prop :=
  aliquotSumNat profile < profileValueNat profile

def AliquotPerfectProfile (profile : PrimePowerProfile) : Prop :=
  aliquotSumNat profile = profileValueNat profile

def AliquotNumberClassProfile (profile : PrimePowerProfile) : Prop :=
  AliquotAbundantProfile profile ∨
    AliquotDeficientProfile profile ∨ AliquotPerfectProfile profile

def AliquotAbundantNumber (n : BHist) : Prop :=
  ∃ profile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      AliquotAbundantProfile profile

def AliquotDeficientNumber (n : BHist) : Prop :=
  ∃ profile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      AliquotDeficientProfile profile

def AliquotPerfectNumber (n : BHist) : Prop :=
  ∃ profile : PrimePowerProfile,
    ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
      AliquotPerfectProfile profile

def AliquotNumberClass (n : BHist) : Prop :=
  AliquotAbundantNumber n ∨ AliquotDeficientNumber n ∨ AliquotPerfectNumber n

inductive AliquotTrace : Nat -> BHist -> BHist -> Prop where
  | zero {n : BHist} : AliquotTrace 0 n n
  | succ {fuel : Nat} {n next out : BHist} :
      AliquotSumNumber n next ->
        AliquotTrace fuel next out ->
          AliquotTrace (fuel + 1) n out

def aliquotIterateWithFuel (step : BHist -> BHist) : Nat -> BHist -> BHist
  | 0, n => n
  | fuel + 1, n => aliquotIterateWithFuel step fuel (step n)

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k ->
      hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

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

theorem aliquotSumNat_eq_sigma_sub_self (profile : PrimePowerProfile) :
    aliquotSumNat profile = sigmaNat profile - profileValueNat profile := by
  rfl

theorem aliquotSum_unary (profile : PrimePowerProfile) :
    UnaryHistory (aliquotSum profile) := by
  unfold aliquotSum
  exact natToUnary_unary _

theorem aliquotSumOfProfile_iff_properDivisorSumOfProfile
    {n s : BHist} {profile : PrimePowerProfile} :
    AliquotSumOfProfile n s profile ↔
      ProperDivisorSumOfProfile n s profile := by
  constructor
  · intro data
    exact ⟨divisorSigmaProfile 1 profile,
      ⟨data.left, data.right.left, hsame_refl (divisorSigmaProfile 1 profile)⟩,
      data.right.right⟩
  · intro data
    cases data with
    | intro _sigma sigmaData =>
        exact ⟨sigmaData.left.left, sigmaData.left.right.left, sigmaData.right⟩

theorem aliquotClassification_trichotomy (profile : PrimePowerProfile) :
    AliquotNumberClassProfile profile := by
  unfold AliquotNumberClassProfile AliquotAbundantProfile
    AliquotDeficientProfile AliquotPerfectProfile
  cases Nat.lt_trichotomy (aliquotSumNat profile) (profileValueNat profile) with
  | inl deficient =>
      exact Or.inr (Or.inl deficient)
  | inr rest =>
      cases rest with
      | inl perfect =>
          exact Or.inr (Or.inr perfect)
      | inr abundant =>
          exact Or.inl abundant

theorem aliquotClassification_exclusive (profile : PrimePowerProfile) :
    (AliquotAbundantProfile profile -> AliquotDeficientProfile profile -> False) ∧
      (AliquotAbundantProfile profile -> AliquotPerfectProfile profile -> False) ∧
        (AliquotDeficientProfile profile -> AliquotPerfectProfile profile -> False) := by
  unfold AliquotAbundantProfile AliquotDeficientProfile AliquotPerfectProfile
  constructor
  · intro abundant deficient
    exact Nat.lt_asymm deficient abundant
  · constructor
    · intro abundant perfect
      exact Nat.lt_irrefl _ (perfect ▸ abundant)
    · intro deficient perfect
      exact Nat.lt_irrefl _ (perfect.symm ▸ deficient)

theorem aliquotClassification_total_with_exclusion
    (profile : PrimePowerProfile) :
    AliquotNumberClassProfile profile ∧
      (AliquotAbundantProfile profile -> AliquotDeficientProfile profile -> False) ∧
        (AliquotAbundantProfile profile -> AliquotPerfectProfile profile -> False) ∧
          (AliquotDeficientProfile profile -> AliquotPerfectProfile profile -> False) := by
  exact ⟨aliquotClassification_trichotomy profile,
    aliquotClassification_exclusive profile⟩

theorem aliquotNumberClass_of_profile
    {n : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile -> PrimeFactorization n (expandProfile profile) ->
      AliquotNumberClass n := by
  intro valid factorization
  cases aliquotClassification_trichotomy profile with
  | inl abundant =>
      exact Or.inl ⟨profile, valid, factorization, abundant⟩
  | inr rest =>
      cases rest with
      | inl deficient =>
          exact Or.inr (Or.inl ⟨profile, valid, factorization, deficient⟩)
      | inr perfect =>
          exact Or.inr (Or.inr ⟨profile, valid, factorization, perfect⟩)

theorem perfectProfile_iff_aliquotPerfectProfile
    (profile : PrimePowerProfile) :
    IsPerfectProfile profile ↔ AliquotPerfectProfile profile := by
  unfold IsPerfectProfile AliquotPerfectProfile aliquotSumNat properDivisorSumNat
  constructor
  · intro sigmaEq
    calc
      sigmaNat profile - profileValueNat profile =
          (2 * profileValueNat profile) - profileValueNat profile := by
            rw [sigmaEq]
      _ =
          (profileValueNat profile + profileValueNat profile) -
            profileValueNat profile := by
              rw [Nat.two_mul]
      _ = profileValueNat profile := natAddSubCancelLeft _ _
  · intro aliquotEq
    have addEq :
        (sigmaNat profile - profileValueNat profile) + profileValueNat profile =
          sigmaNat profile :=
      natSubAddCancelOfLe _ _ (profileValueNat_le_sigmaNat profile)
    calc
      sigmaNat profile =
          (sigmaNat profile - profileValueNat profile) +
            profileValueNat profile := addEq.symm
      _ = profileValueNat profile + profileValueNat profile := by
            rw [aliquotEq]
      _ = 2 * profileValueNat profile := (Nat.two_mul _).symm

theorem perfectNumber_iff_aliquotPerfectNumber (n : BHist) :
    PerfectNumber n ↔ AliquotPerfectNumber n := by
  constructor
  · intro perfect
    cases perfect with
    | intro profile data =>
        exact ⟨profile, data.left, data.right.left,
          (perfectProfile_iff_aliquotPerfectProfile profile).mp data.right.right⟩
  · intro perfect
    cases perfect with
    | intro profile data =>
        exact ⟨profile, data.left, data.right.left,
          (perfectProfile_iff_aliquotPerfectProfile profile).mpr data.right.right⟩

theorem primeFlatProductNat_append (xs ys : List BHist) :
    primeFlatProductNat (xs ++ ys) =
      primeFlatProductNat xs * primeFlatProductNat ys := by
  induction xs with
  | nil =>
      change primeFlatProductNat ys = 1 * primeFlatProductNat ys
      rw [Nat.one_mul]
  | cons p ps ih =>
      change
        bwordLength p * primeFlatProductNat (ps ++ ys) =
          (bwordLength p * primeFlatProductNat ps) * primeFlatProductNat ys
      rw [ih]
      exact (nat_mul_assoc_pure (bwordLength p)
        (primeFlatProductNat ps) (primeFlatProductNat ys)).symm

theorem primeFlatProductNat_expandPrimePower (p : BHist) :
    ∀ exponent : Nat,
      primeFlatProductNat (expandPrimePower p exponent) =
        natPow (bwordLength p) exponent
  | 0 => by
      rfl
  | exponent + 1 => by
      change
        bwordLength p * primeFlatProductNat (expandPrimePower p exponent) =
          bwordLength p * natPow (bwordLength p) exponent
      exact congrArg (fun t => bwordLength p * t)
        (primeFlatProductNat_expandPrimePower p exponent)

theorem primeFlatProductNat_expandProfile
    (profile : PrimePowerProfile) :
    primeFlatProductNat (expandProfile profile) = profileValueNat profile := by
  induction profile with
  | nil =>
      rfl
  | cons e es ih =>
      change
        primeFlatProductNat (expandPrimePower e.prime e.exponent ++ expandProfile es) =
          natPow (bwordLength e.prime) e.exponent * profileValueNat es
      rw [primeFlatProductNat_append, primeFlatProductNat_expandPrimePower, ih]

theorem natToUnary_profileValue_hsame_of_factorization
    {n : BHist} {profile : PrimePowerProfile} :
    PrimeFactorization n (expandProfile profile) ->
      hsame (natToUnary (profileValueNat profile)) n := by
  intro factorization
  have sameProduct :
      hsame (primePowerProduct (expandProfile profile)) n :=
    primePowerProduct_eq_flat factorization.right
  have sameValueProduct :
      hsame (natToUnary (profileValueNat profile))
        (primePowerProduct (expandProfile profile)) := by
    apply unary_hsame_of_length
    · exact natToUnary_unary _
    · exact primePowerProduct_unary (expandProfile profile)
    · unfold primePowerProduct
      rw [natToUnary_length, natToUnary_length,
        primePowerProductNat_eq_flat, primeFlatProductNat_expandProfile]
  exact hsame_trans sameValueProduct sameProduct

theorem aliquotPerfectProfile_to_fixed
    {n : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile -> PrimeFactorization n (expandProfile profile) ->
      AliquotPerfectProfile profile -> AliquotSumOfProfile n n profile := by
  intro valid factorization perfect
  have sameValueN :
      hsame (natToUnary (profileValueNat profile)) n :=
    natToUnary_profileValue_hsame_of_factorization factorization
  have sameNValue :
      hsame n (natToUnary (profileValueNat profile)) :=
    hsame_symm sameValueN
  have sameValueAliquot :
      hsame (natToUnary (profileValueNat profile)) (aliquotSum profile) := by
    apply unary_hsame_of_length
    · exact natToUnary_unary _
    · exact aliquotSum_unary profile
    · unfold aliquotSum
      rw [natToUnary_length, natToUnary_length]
      exact perfect.symm
  exact ⟨valid, factorization, hsame_trans sameNValue sameValueAliquot⟩

theorem aliquotFixed_to_perfectProfile
    {n : BHist} {profile : PrimePowerProfile} :
    AliquotSumOfProfile n n profile -> AliquotPerfectProfile profile := by
  intro fixed
  have sameValueN :
      hsame (natToUnary (profileValueNat profile)) n :=
    natToUnary_profileValue_hsame_of_factorization fixed.right.left
  have sameValueAliquot :
      hsame (natToUnary (profileValueNat profile)) (aliquotSum profile) :=
    hsame_trans sameValueN fixed.right.right
  have lengthEq :
      profileValueNat profile = aliquotSumNat profile := by
    have raw := congrArg bwordLength sameValueAliquot
    unfold aliquotSum at raw
    rw [natToUnary_length, natToUnary_length] at raw
    exact raw
  exact lengthEq.symm

theorem perfectNumber_iff_aliquotSum_eq_self (n : BHist) :
    PerfectNumber n ↔ AliquotFixedNumber n := by
  constructor
  · intro perfect
    cases perfect with
    | intro profile data =>
        exact ⟨profile, aliquotPerfectProfile_to_fixed data.left data.right.left
          ((perfectProfile_iff_aliquotPerfectProfile profile).mp data.right.right)⟩
  · intro fixed
    cases fixed with
    | intro profile data =>
        exact ⟨profile, data.left, data.right.left,
          (perfectProfile_iff_aliquotPerfectProfile profile).mpr
            (aliquotFixed_to_perfectProfile data)⟩

theorem aliquotTrace_zero (n : BHist) :
    AliquotTrace 0 n n := by
  exact AliquotTrace.zero

theorem aliquotTrace_succ
    {fuel : Nat} {n next out : BHist} :
    AliquotSumNumber n next ->
      AliquotTrace fuel next out ->
        AliquotTrace (fuel + 1) n out := by
  exact AliquotTrace.succ

theorem aliquotIterateWithFuel_zero
    (step : BHist -> BHist) (n : BHist) :
    aliquotIterateWithFuel step 0 n = n := by
  rfl

theorem aliquotIterateWithFuel_succ
    (step : BHist -> BHist) (fuel : Nat) (n : BHist) :
    aliquotIterateWithFuel step (fuel + 1) n =
      aliquotIterateWithFuel step fuel (step n) := by
  rfl

theorem six_aliquot_fixed :
    AliquotFixedNumber NatSix := by
  exact (perfectNumber_iff_aliquotSum_eq_self NatSix).mp perfect_six_number

theorem eight_aliquot_deficient_profile :
    AliquotDeficientProfile profileEight := by
  unfold AliquotDeficientProfile aliquotSumNat
  rw [properDivisorSumEight_value, profileEight_value]
  decide

theorem twelve_aliquot_abundant_profile :
    AliquotAbundantProfile profileTwelve := by
  unfold AliquotAbundantProfile aliquotSumNat
  rw [properDivisorSumTwelve_value, profileTwelve_value]
  decide

end BEDC.Derived.AliquotSequenceUp
