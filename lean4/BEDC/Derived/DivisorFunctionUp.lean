import BEDC.Derived.ArithmeticFnUp

namespace BEDC.Derived.DivisorFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.GcdUp
open BEDC.Derived.PadicUp (NatOne)
open BEDC.Derived.ArithmeticFnUp

structure PrimePowerEntry where
  prime : BHist
  exponent : Nat

abbrev PrimePowerProfile := List PrimePowerEntry

def expandPrimePower (p : BHist) : Nat -> List BHist
  | 0 => []
  | a + 1 => p :: expandPrimePower p a

def expandProfile : PrimePowerProfile -> List BHist
  | [] => []
  | e :: es => expandPrimePower e.prime e.exponent ++ expandProfile es

def profilePrimes : PrimePowerProfile -> List BHist
  | [] => []
  | e :: es => e.prime :: profilePrimes es

inductive ProfileValid : PrimePowerProfile -> Prop where
  | nil : ProfileValid []
  | cons {e : PrimePowerEntry} {es : PrimePowerProfile} :
      NatPrime e.prime ->
        (e.exponent = 0 -> False) ->
          listContainsPrime e.prime (profilePrimes es) = false ->
            ProfileValid es -> ProfileValid (e :: es)

def divisorCountProfileNat : PrimePowerProfile -> Nat
  | [] => 1
  | e :: es => (e.exponent + 1) * divisorCountProfileNat es

def divisorSigmaPowerFactorNat (k : Nat) (p : BHist) : Nat -> Nat
  | 0 => 1
  | a + 1 =>
      divisorSigmaPowerFactorNat k p a +
        natPow (bwordLength p) (k * (a + 1))

def divisorSigmaProfileNat (k : Nat) : PrimePowerProfile -> Nat
  | [] => 1
  | e :: es =>
      divisorSigmaPowerFactorNat k e.prime e.exponent *
        divisorSigmaProfileNat k es

def divisorCountProfile (profile : PrimePowerProfile) : BHist :=
  natToUnary (divisorCountProfileNat profile)

def divisorSigmaProfile (k : Nat) (profile : PrimePowerProfile) : BHist :=
  natToUnary (divisorSigmaProfileNat k profile)

def divisorCountEnumerationValue (ds : List BHist) : BHist :=
  natToUnary ds.length

def divisorPowerSumNat (k : Nat) : List BHist -> Nat
  | [] => 0
  | d :: ds => natPow (bwordLength d) k + divisorPowerSumNat k ds

def divisorSigmaEnumerationValue (k : Nat) (ds : List BHist) : BHist :=
  natToUnary (divisorPowerSumNat k ds)

def DivisorCountByDivisorEnumeration (n count : BHist) : Prop :=
  ∃ ds : List BHist,
    divisors n ds ∧ hsame count (divisorCountEnumerationValue ds)

def DivisorSigmaByDivisorEnumeration (k : Nat) (n sigma : BHist) : Prop :=
  ∃ ds : List BHist,
    divisors n ds ∧ hsame sigma (divisorSigmaEnumerationValue k ds)

def DivisorCountOfProfile (n count : BHist) (profile : PrimePowerProfile) : Prop :=
  ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
    hsame count (divisorCountProfile profile)

def DivisorSigmaOfProfile
    (k : Nat) (n sigma : BHist) (profile : PrimePowerProfile) : Prop :=
  ProfileValid profile ∧ PrimeFactorization n (expandProfile profile) ∧
    hsame sigma (divisorSigmaProfile k profile)

def DivisorCountOfFactorization (n count : BHist) : Prop :=
  ∃ profile : PrimePowerProfile, DivisorCountOfProfile n count profile

def DivisorSigmaOfFactorization (k : Nat) (n sigma : BHist) : Prop :=
  ∃ profile : PrimePowerProfile, DivisorSigmaOfProfile k n sigma profile

theorem expandPrimePower_append (p : BHist) :
    ∀ a b : Nat,
      expandPrimePower p (a + b) =
        expandPrimePower p a ++ expandPrimePower p b
  | 0, b => by
      rw [Nat.zero_add]
      rfl
  | a + 1, b => by
      rw [Nat.succ_add]
      change p :: expandPrimePower p (a + b) =
        p :: (expandPrimePower p a ++ expandPrimePower p b)
      exact congrArg (fun xs => p :: xs) (expandPrimePower_append p a b)

theorem profilePrimes_append (xs ys : PrimePowerProfile) :
    profilePrimes (xs ++ ys) = profilePrimes xs ++ profilePrimes ys := by
  induction xs with
  | nil =>
      rfl
  | cons e es ih =>
      change e.prime :: profilePrimes (es ++ ys) =
        e.prime :: (profilePrimes es ++ profilePrimes ys)
      exact congrArg (fun tail => e.prime :: tail) ih

private theorem listContainsPrime_append_false_local {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = false -> listContainsPrime p ys = false ->
        listContainsPrime p (xs ++ ys) = false := by
  intro xs
  induction xs with
  | nil =>
      intro ys _absentLeft absentRight
      exact absentRight
  | cons q qs ih =>
      intro ys absentLeft absentRight
      change (if p = q then true else listContainsPrime p qs) = false at absentLeft
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = false
      by_cases same : p = q
      · rw [if_pos same] at absentLeft
        cases absentLeft
      · rw [if_neg same] at absentLeft
        rw [if_neg same]
        exact ih ys absentLeft absentRight

private theorem listContainsPrime_append_true_left_local {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = true -> listContainsPrime p (xs ++ ys) = true := by
  intro xs
  induction xs with
  | nil =>
      intro ys found
      cases found
  | cons q qs ih =>
      intro ys found
      change (if p = q then true else listContainsPrime p qs) = true at found
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = true
      by_cases same : p = q
      · rw [if_pos same]
      · rw [if_neg same] at found
        rw [if_neg same]
        exact ih ys found

private theorem listContainsPrime_append_true_right_local {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p ys = true -> listContainsPrime p (xs ++ ys) = true := by
  intro xs
  induction xs with
  | nil =>
      intro ys found
      exact found
  | cons q qs ih =>
      intro ys found
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = true
      by_cases same : p = q
      · rw [if_pos same]
      · rw [if_neg same]
        exact ih ys found

private theorem listNoCommonPrime_append_left_tail_local
    (pref xs ys : List BHist) :
    listNoCommonPrime (pref ++ xs) ys -> listNoCommonPrime xs ys := by
  intro common
  induction pref with
  | nil =>
      exact common
  | cons _p ps ih =>
      exact ih common.right

private theorem expandPrimePower_no_common_head_absent
    (p : BHist) :
    ∀ a : Nat, (a = 0 -> False) ->
      ∀ tail ys : List BHist,
        listNoCommonPrime (expandPrimePower p a ++ tail) ys ->
          listContainsPrime p ys = false
  | 0, nonzero, _tail, _ys, _common => False.elim (nonzero rfl)
  | a + 1, _nonzero, tail, ys, common => by
      change listNoCommonPrime (p :: (expandPrimePower p a ++ tail)) ys at common
      exact common.left

private theorem expandPrimePower_no_common_tail
    (p : BHist) :
    ∀ a : Nat, (a = 0 -> False) ->
      ∀ tail ys : List BHist,
        listNoCommonPrime (expandPrimePower p a ++ tail) ys ->
          listNoCommonPrime tail ys
  | 0, nonzero, _tail, _ys, _common => False.elim (nonzero rfl)
  | a + 1, _nonzero, tail, ys, common => by
      change listNoCommonPrime (p :: (expandPrimePower p a ++ tail)) ys at common
      exact listNoCommonPrime_append_left_tail_local
        (expandPrimePower p a) tail ys common.right

private theorem expandPrimePower_contains_self
    (p : BHist) :
    ∀ a : Nat, (a = 0 -> False) ->
      listContainsPrime p (expandPrimePower p a) = true
  | 0, nonzero => False.elim (nonzero rfl)
  | _a + 1, _nonzero => by
      change (if p = p then true else listContainsPrime p (expandPrimePower p _)) = true
      rw [if_pos rfl]

private theorem profileContains_implies_expandContains
    {p : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile ->
      listContainsPrime p (profilePrimes profile) = true ->
        listContainsPrime p (expandProfile profile) = true := by
  revert profile
  intro profile
  induction profile with
  | nil =>
      intro _valid found
      cases found
  | cons e es ih =>
      intro valid found
      cases valid with
      | cons _ePrime eNonzero _absentTail validTail =>
      change (if p = e.prime then true else listContainsPrime p (profilePrimes es)) =
        true at found
      change listContainsPrime p
        (expandPrimePower e.prime e.exponent ++ expandProfile es) = true
      by_cases same : p = e.prime
      · cases same
        exact listContainsPrime_append_true_left_local
          (expandPrimePower e.prime e.exponent) (expandProfile es)
          (expandPrimePower_contains_self e.prime e.exponent eNonzero)
      · rw [if_neg same] at found
        exact listContainsPrime_append_true_right_local
          (expandPrimePower e.prime e.exponent) (expandProfile es)
          (ih validTail found)

private theorem listContainsPrime_profile_false_of_expand_false
    {p : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile ->
      listContainsPrime p (expandProfile profile) = false ->
        listContainsPrime p (profilePrimes profile) = false := by
  intro valid absentExpanded
  cases found : listContainsPrime p (profilePrimes profile)
  · rfl
  · have foundExpanded := profileContains_implies_expandContains valid found
    rw [absentExpanded] at foundExpanded
    cases foundExpanded

theorem profilePrimes_no_common_of_expandProfile_no_common
    {xs ys : PrimePowerProfile} :
    ProfileValid xs -> ProfileValid ys ->
      listNoCommonPrime (expandProfile xs) (expandProfile ys) ->
        listNoCommonPrime (profilePrimes xs) (profilePrimes ys) := by
  revert xs ys
  intro xs
  induction xs with
  | nil =>
      intro ys
      intro _validX _validY _common
      trivial
  | cons e es ih =>
      intro ys
      intro validX validY common
      cases validX with
      | cons _ePrime eNonzero _absentTail validTail =>
      change listNoCommonPrime (e.prime :: profilePrimes es) (profilePrimes ys)
      unfold listNoCommonPrime
      constructor
      · have absentExpanded :
          listContainsPrime e.prime (expandProfile ys) = false := by
            change listNoCommonPrime
              (expandPrimePower e.prime e.exponent ++ expandProfile es)
              (expandProfile ys) at common
            exact expandPrimePower_no_common_head_absent e.prime e.exponent
              eNonzero (expandProfile es) (expandProfile ys) common
        exact listContainsPrime_profile_false_of_expand_false validY absentExpanded
      · have tailCommon :
          listNoCommonPrime (expandProfile es) (expandProfile ys) := by
            change listNoCommonPrime
              (expandPrimePower e.prime e.exponent ++ expandProfile es)
              (expandProfile ys) at common
            exact expandPrimePower_no_common_tail e.prime e.exponent
              eNonzero (expandProfile es) (expandProfile ys) common
        exact ih validTail validY tailCommon

theorem ProfileValid_append_disjoint
    {xs ys : PrimePowerProfile} :
    ProfileValid xs -> ProfileValid ys ->
      listNoCommonPrime (profilePrimes xs) (profilePrimes ys) ->
        ProfileValid (xs ++ ys) := by
  revert xs ys
  intro xs
  induction xs with
  | nil =>
      intro ys
      intro _validX validY _common
      exact validY
  | cons e es ih =>
      intro ys
      intro validX validY common
      cases validX with
      | cons ePrime eNonzero absentTail validTail =>
      change ProfileValid (_ :: (_ ++ ys))
      apply ProfileValid.cons ePrime eNonzero
      · rw [profilePrimes_append]
        change listNoCommonPrime (e.prime :: profilePrimes es) (profilePrimes ys) at common
        unfold listNoCommonPrime at common
        exact listContainsPrime_append_false_local
          (profilePrimes es) (profilePrimes ys) absentTail common.left
      · unfold listNoCommonPrime at common
        exact ih validTail validY common.right

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

theorem divisorCountProfile_unary (profile : PrimePowerProfile) :
    UnaryHistory (divisorCountProfile profile) := by
  unfold divisorCountProfile
  exact natToUnary_unary _

theorem divisorSigmaProfile_unary (k : Nat) (profile : PrimePowerProfile) :
    UnaryHistory (divisorSigmaProfile k profile) := by
  unfold divisorSigmaProfile
  exact natToUnary_unary _

theorem divisorCountProfileNat_append
    (xs ys : PrimePowerProfile) :
    divisorCountProfileNat (xs ++ ys) =
      divisorCountProfileNat xs * divisorCountProfileNat ys := by
  induction xs with
  | nil =>
      change divisorCountProfileNat ys = 1 * divisorCountProfileNat ys
      rw [Nat.one_mul]
  | cons e es ih =>
      change
        (e.exponent + 1) * divisorCountProfileNat (es ++ ys) =
          ((e.exponent + 1) * divisorCountProfileNat es) * divisorCountProfileNat ys
      rw [ih]
      exact (nat_mul_assoc_pure (e.exponent + 1)
        (divisorCountProfileNat es) (divisorCountProfileNat ys)).symm

theorem divisorSigmaProfileNat_append
    (k : Nat) (xs ys : PrimePowerProfile) :
    divisorSigmaProfileNat k (xs ++ ys) =
      divisorSigmaProfileNat k xs * divisorSigmaProfileNat k ys := by
  induction xs with
  | nil =>
      change divisorSigmaProfileNat k ys = 1 * divisorSigmaProfileNat k ys
      rw [Nat.one_mul]
  | cons e es ih =>
      change
        divisorSigmaPowerFactorNat k e.prime e.exponent *
            divisorSigmaProfileNat k (es ++ ys) =
          (divisorSigmaPowerFactorNat k e.prime e.exponent *
              divisorSigmaProfileNat k es) *
            divisorSigmaProfileNat k ys
      rw [ih]
      exact (nat_mul_assoc_pure (divisorSigmaPowerFactorNat k e.prime e.exponent)
        (divisorSigmaProfileNat k es) (divisorSigmaProfileNat k ys)).symm

def divisorCountMultiplicativeValue
    (xs ys : PrimePowerProfile) : BHist :=
  natToUnary (divisorCountProfileNat xs * divisorCountProfileNat ys)

def divisorSigmaMultiplicativeValue
    (k : Nat) (xs ys : PrimePowerProfile) : BHist :=
  natToUnary (divisorSigmaProfileNat k xs * divisorSigmaProfileNat k ys)

theorem divisorCount_profile_append_hsame
    (xs ys : PrimePowerProfile) :
    hsame (divisorCountProfile (xs ++ ys))
      (divisorCountMultiplicativeValue xs ys) := by
  apply unary_hsame_of_length
  · exact divisorCountProfile_unary (xs ++ ys)
  · unfold divisorCountMultiplicativeValue
    exact natToUnary_unary _
  · unfold divisorCountProfile divisorCountMultiplicativeValue
    rw [natToUnary_length, natToUnary_length]
    exact divisorCountProfileNat_append xs ys

theorem divisorSigma_profile_append_hsame
    (k : Nat) (xs ys : PrimePowerProfile) :
    hsame (divisorSigmaProfile k (xs ++ ys))
      (divisorSigmaMultiplicativeValue k xs ys) := by
  apply unary_hsame_of_length
  · exact divisorSigmaProfile_unary k (xs ++ ys)
  · unfold divisorSigmaMultiplicativeValue
    exact natToUnary_unary _
  · unfold divisorSigmaProfile divisorSigmaMultiplicativeValue
    rw [natToUnary_length, natToUnary_length]
    exact divisorSigmaProfileNat_append k xs ys

theorem PrimeFactorizationProduct_profile_append_mul
    {xs ys : PrimePowerProfile} {m n mn : BHist} :
    PrimeFactorizationProduct (expandProfile xs) m ->
      PrimeFactorizationProduct (expandProfile ys) n ->
        NatMul m n mn ->
          PrimeFactorizationProduct (expandProfile (xs ++ ys)) mn := by
  induction xs generalizing m mn with
  | nil =>
      intro fx fy mul
      have shifted : NatMul NatOne n mn :=
        (NatMul_multiplicand_hsame_transport fx mul).right
      have sameNMn : hsame n mn :=
        hsame_symm (NatMul_unit_left_hsame
          (PrimeFactorizationProduct_result_unary fy) shifted)
      exact PrimeFactorizationProduct_result_hsame_transport fy sameNMn
  | cons e es ih =>
      cases e with
      | mk p exponent =>
      intro fx fy mul
      change PrimeFactorizationProduct
        (expandPrimePower p exponent ++ expandProfile es) m at fx
      change PrimeFactorizationProduct
        (expandPrimePower p exponent ++ expandProfile (es ++ ys)) mn
      induction exponent generalizing m mn with
      | zero =>
          change PrimeFactorizationProduct (expandProfile es) m at fx
          change PrimeFactorizationProduct (expandProfile (es ++ ys)) mn
          exact ih fx fy mul
      | succ a expIh =>
          change PrimeFactorizationProduct
            (p :: (expandPrimePower p a ++ expandProfile es)) m at fx
          change PrimeFactorizationProduct
            (p :: (expandPrimePower p a ++ expandProfile (es ++ ys))) mn
          cases fx with
          | intro pPrime tailWitness =>
              cases tailWitness with
              | intro tailProduct tailData =>
                  have tailUnary : UnaryHistory tailProduct :=
                    PrimeFactorizationProduct_result_unary tailData.left
                  have nUnary : UnaryHistory n :=
                    PrimeFactorizationProduct_result_unary fy
                  cases NatMul_total tailUnary nUnary with
                  | intro tailN tailNData =>
                      have tailProductFactor :
                          PrimeFactorizationProduct
                            (expandPrimePower p a ++ expandProfile (es ++ ys)) tailN :=
                        expIh tailNData.right tailData.left
                      have tailNUnary : UnaryHistory tailN := tailNData.left
                      cases NatMul_total pPrime.left tailNUnary with
                      | intro displayed displayedData =>
                          have sameMnDisplayed : hsame mn displayed :=
                            NatMul_assoc_hsame pPrime.left tailUnary nUnary
                              tailData.right mul tailNData.right displayedData.right
                          have pTailNAtMn : NatMul p tailN mn :=
                            (NatMul_result_hsame_transport displayedData.right
                              (hsame_symm sameMnDisplayed)).right
                          exact ⟨pPrime, tailN, tailProductFactor, pTailNAtMn⟩

theorem divisorCount_by_divisor_enumeration_of_factorization
    {n : BHist} {entries : List BHist} :
    PrimeFactorization n entries ->
      DivisorCountByDivisorEnumeration n
        (divisorCountEnumerationValue (divisorProductsOfFactorization entries)) := by
  intro factorization
  exact ⟨divisorProductsOfFactorization entries,
    divisors_of_factorization factorization,
    hsame_refl (divisorCountEnumerationValue (divisorProductsOfFactorization entries))⟩

theorem divisorSigma_by_divisor_enumeration_of_factorization
    (k : Nat) {n : BHist} {entries : List BHist} :
    PrimeFactorization n entries ->
      DivisorSigmaByDivisorEnumeration k n
        (divisorSigmaEnumerationValue k (divisorProductsOfFactorization entries)) := by
  intro factorization
  exact ⟨divisorProductsOfFactorization entries,
    divisors_of_factorization factorization,
    hsame_refl
      (divisorSigmaEnumerationValue k (divisorProductsOfFactorization entries))⟩

theorem divisorCount_of_profile
    {n : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile -> PrimeFactorization n (expandProfile profile) ->
      DivisorCountOfFactorization n (divisorCountProfile profile) := by
  intro valid factorization
  exact ⟨profile, valid, factorization, hsame_refl (divisorCountProfile profile)⟩

theorem divisorSigma_of_profile
    {k : Nat} {n : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile -> PrimeFactorization n (expandProfile profile) ->
      DivisorSigmaOfFactorization k n (divisorSigmaProfile k profile) := by
  intro valid factorization
  exact ⟨profile, valid, factorization, hsame_refl (divisorSigmaProfile k profile)⟩

theorem divisorCount_profile_product_append
    {m n mn : BHist} {xs ys : PrimePowerProfile} :
    ProfileValid xs -> ProfileValid ys ->
      listNoCommonPrime (profilePrimes xs) (profilePrimes ys) ->
        PrimeFactorizationProduct (expandProfile xs) m ->
          PrimeFactorizationProduct (expandProfile ys) n ->
            NatMul m n mn ->
              DivisorCountOfFactorization mn
                (divisorCountMultiplicativeValue xs ys) := by
  intro validX validY primeDisjoint fx fy mul
  have validAppend : ProfileValid (xs ++ ys) :=
    ProfileValid_append_disjoint validX validY primeDisjoint
  have product : PrimeFactorizationProduct (expandProfile (xs ++ ys)) mn := by
    exact PrimeFactorizationProduct_profile_append_mul fx fy mul
  have sameCount :
      hsame (divisorCountMultiplicativeValue xs ys)
        (divisorCountProfile (xs ++ ys)) :=
    hsame_symm (divisorCount_profile_append_hsame xs ys)
  exact ⟨xs ++ ys,
    validAppend,
    ⟨NatMul_result_unary (PrimeFactorizationProduct_result_unary fx) mul, product⟩,
    sameCount⟩

theorem divisorSigma_profile_product_append
    {k : Nat} {m n mn : BHist} {xs ys : PrimePowerProfile} :
    ProfileValid xs -> ProfileValid ys ->
      listNoCommonPrime (profilePrimes xs) (profilePrimes ys) ->
        PrimeFactorizationProduct (expandProfile xs) m ->
          PrimeFactorizationProduct (expandProfile ys) n ->
            NatMul m n mn ->
              DivisorSigmaOfFactorization k mn
                (divisorSigmaMultiplicativeValue k xs ys) := by
  intro validX validY primeDisjoint fx fy mul
  have validAppend : ProfileValid (xs ++ ys) :=
    ProfileValid_append_disjoint validX validY primeDisjoint
  have product : PrimeFactorizationProduct (expandProfile (xs ++ ys)) mn := by
    exact PrimeFactorizationProduct_profile_append_mul fx fy mul
  have sameSigma :
      hsame (divisorSigmaMultiplicativeValue k xs ys)
        (divisorSigmaProfile k (xs ++ ys)) :=
    hsame_symm (divisorSigma_profile_append_hsame k xs ys)
  exact ⟨xs ++ ys,
    validAppend,
    ⟨NatMul_result_unary (PrimeFactorizationProduct_result_unary fx) mul, product⟩,
    sameSigma⟩

theorem divisorCount_profile_product_multiplicative_of_gcd_one
    {m n mn : BHist} {xs ys : PrimePowerProfile} :
    ProfileValid xs -> ProfileValid ys ->
      PrimeFactorizationProduct (expandProfile xs) m ->
        PrimeFactorizationProduct (expandProfile ys) n ->
          NatMul m n mn ->
            NatGcd m n NatOne ->
            DivisorCountOfFactorization mn
              (divisorCountMultiplicativeValue xs ys) ∧
              listNoCommonPrime (expandProfile xs) (expandProfile ys) := by
  intro validX validY fx fy mul gcd
  have expandDisjoint : listNoCommonPrime (expandProfile xs) (expandProfile ys) :=
    PrimeFactorizationProduct_coprime_no_common fx fy gcd
  have primeDisjoint : listNoCommonPrime (profilePrimes xs) (profilePrimes ys) :=
    profilePrimes_no_common_of_expandProfile_no_common validX validY expandDisjoint
  exact ⟨divisorCount_profile_product_append validX validY primeDisjoint fx fy mul,
    expandDisjoint⟩

theorem divisorSigma_profile_product_multiplicative_of_gcd_one
    {k : Nat} {m n mn : BHist} {xs ys : PrimePowerProfile} :
    ProfileValid xs -> ProfileValid ys ->
      PrimeFactorizationProduct (expandProfile xs) m ->
        PrimeFactorizationProduct (expandProfile ys) n ->
          NatMul m n mn ->
            NatGcd m n NatOne ->
            DivisorSigmaOfFactorization k mn
              (divisorSigmaMultiplicativeValue k xs ys) ∧
              listNoCommonPrime (expandProfile xs) (expandProfile ys) := by
  intro validX validY fx fy mul gcd
  have expandDisjoint : listNoCommonPrime (expandProfile xs) (expandProfile ys) :=
    PrimeFactorizationProduct_coprime_no_common fx fy gcd
  have primeDisjoint : listNoCommonPrime (profilePrimes xs) (profilePrimes ys) :=
    profilePrimes_no_common_of_expandProfile_no_common validX validY expandDisjoint
  exact ⟨divisorSigma_profile_product_append validX validY primeDisjoint fx fy mul,
    expandDisjoint⟩

theorem divisorCount_prime_power_formula
    (p : BHist) (a : Nat) :
    divisorCountProfileNat [{ prime := p, exponent := a }] = a + 1 := by
  change (a + 1) * 1 = a + 1
  rw [Nat.mul_one]

theorem divisorSigma_prime_power_formula
    (k : Nat) (p : BHist) (a : Nat) :
    divisorSigmaProfileNat k [{ prime := p, exponent := a }] =
      divisorSigmaPowerFactorNat k p a := by
  change divisorSigmaPowerFactorNat k p a * 1 =
    divisorSigmaPowerFactorNat k p a
  rw [Nat.mul_one]

def NatTwo : BHist := BHist.e1 NatOne
def NatThree : BHist := BHist.e1 NatTwo

private theorem natOne_unary : UnaryHistory NatOne :=
  unary_e1_closed unary_empty

private theorem natTwo_unary : UnaryHistory NatTwo := by
  unfold NatTwo
  exact unary_e1_closed natOne_unary

private theorem natThree_unary : UnaryHistory NatThree := by
  unfold NatThree
  exact unary_e1_closed natTwo_unary

theorem divisorCount_one :
    DivisorCountOfFactorization NatOne NatOne := by
  exact ⟨[], ProfileValid.nil, ⟨natOne_unary, hsame_refl NatOne⟩,
    hsame_refl NatOne⟩

theorem divisorSigma_one (k : Nat) :
    DivisorSigmaOfFactorization k NatOne NatOne := by
  exact ⟨[], ProfileValid.nil, ⟨natOne_unary, hsame_refl NatOne⟩,
    hsame_refl NatOne⟩

theorem divisorSigma_profile_single_prime_value
    (k : Nat) (p : BHist) :
    divisorSigmaProfileNat k [{ prime := p, exponent := 1 }] =
      1 + natPow (bwordLength p) k := by
  change (1 + natPow (bwordLength p) (k * 1)) * 1 =
    1 + natPow (bwordLength p) k
  rw [Nat.mul_one, Nat.mul_one]

theorem divisorCount_single_prime_value
    {p : BHist} :
    NatPrime p -> DivisorCountOfFactorization p NatTwo := by
  intro pPrime
  have product : PrimeFactorizationProduct [p] p := by
    exact ⟨pPrime, NatOne, hsame_refl NatOne,
      NatMul.succ (NatMul.zero pPrime.left) (BEDC.FKernel.Cont.cont_left_unit p)⟩
  have countSame : hsame NatTwo
      (divisorCountProfile [{ prime := p, exponent := 1 }]) := by
    apply unary_hsame_of_length
    · exact natTwo_unary
    · exact divisorCountProfile_unary [{ prime := p, exponent := 1 }]
    · unfold NatTwo divisorCountProfile divisorCountProfileNat
      rw [natToUnary_length]
      rfl
  have valid : ProfileValid [{ prime := p, exponent := 1 }] :=
    ProfileValid.cons pPrime (by intro contradiction; cases contradiction) rfl
      ProfileValid.nil
  exact ⟨[{ prime := p, exponent := 1 }],
    valid, ⟨pPrime.left, product⟩, countSame⟩

theorem divisorCount_square_prime_value
    {p pp : BHist} :
    NatPrime p -> NatMul p p pp -> DivisorCountOfFactorization pp NatThree := by
  intro pPrime square
  have productTail : PrimeFactorizationProduct [p] p := by
    exact ⟨pPrime, NatOne, hsame_refl NatOne,
      NatMul.succ (NatMul.zero pPrime.left) (BEDC.FKernel.Cont.cont_left_unit p)⟩
  have product : PrimeFactorizationProduct [p, p] pp := by
    exact ⟨pPrime, p, productTail, square⟩
  have countSame : hsame NatThree
      (divisorCountProfile [{ prime := p, exponent := 2 }]) := by
    apply unary_hsame_of_length
    · exact natThree_unary
    · exact divisorCountProfile_unary [{ prime := p, exponent := 2 }]
    · unfold NatThree NatTwo divisorCountProfile divisorCountProfileNat
      rw [natToUnary_length]
      rfl
  have valid : ProfileValid [{ prime := p, exponent := 2 }] :=
    ProfileValid.cons pPrime (by intro contradiction; cases contradiction) rfl
      ProfileValid.nil
  exact ⟨[{ prime := p, exponent := 2 }],
    valid, ⟨NatMul_result_unary pPrime.left square, product⟩, countSame⟩

end BEDC.Derived.DivisorFunctionUp
