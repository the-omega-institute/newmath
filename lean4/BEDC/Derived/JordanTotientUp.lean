import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.MobiusInversionUp
import BEDC.Derived.PrimeUp.UniqueFactorization

namespace BEDC.Derived.JordanTotientUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp (NatOne)
open BEDC.Derived.PrimeUp

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

private theorem natPow_zero_exp (base : Nat) :
    natPow base 0 = 1 := by
  rfl

private theorem natPow_one_exp (base : Nat) :
    natPow base 1 = base := by
  change base * 1 = base
  rw [Nat.mul_one]

private theorem natPow_one_base :
    ∀ exp : Nat, natPow 1 exp = 1
  | 0 => rfl
  | exp + 1 => by
      change 1 * natPow 1 exp = 1
      rw [Nat.one_mul, natPow_one_base exp]

private theorem natPow_add (base a b : Nat) :
    natPow base (a + b) = natPow base a * natPow base b := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      change natPow base b = 1 * natPow base b
      rw [Nat.one_mul]
  | succ a ih =>
      rw [Nat.succ_add]
      change base * natPow base (a + b) =
        (base * natPow base a) * natPow base b
      rw [ih]
      exact (nat_mul_assoc_pure base (natPow base a) (natPow base b)).symm

private theorem natPow_mul_right (base a b : Nat) :
    natPow (natPow base a) b = natPow base (a * b) := by
  induction b with
  | zero =>
      rw [Nat.mul_zero]
      rfl
  | succ b ih =>
      change natPow base a * natPow (natPow base a) b =
        natPow base (a * Nat.succ b)
      rw [ih, Nat.mul_succ, natPow_add]
      exact Nat.mul_comm _ _

private theorem nat_mul_pair_swap (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  calc
    (a * b) * (c * d) = a * (b * (c * d)) := nat_mul_assoc_pure a b (c * d)
    _ = a * ((b * c) * d) :=
      congrArg (fun x => a * x) (nat_mul_assoc_pure b c d).symm
    _ = a * ((c * b) * d) :=
      congrArg (fun x => a * (x * d)) (Nat.mul_comm b c)
    _ = a * (c * (b * d)) :=
      congrArg (fun x => a * x) (nat_mul_assoc_pure c b d)
    _ = (a * c) * (b * d) := (nat_mul_assoc_pure a c (b * d)).symm

private theorem natPow_mul_base (a b exp : Nat) :
    natPow (a * b) exp = natPow a exp * natPow b exp := by
  induction exp with
  | zero =>
      change 1 = 1 * 1
      rw [Nat.mul_one]
  | succ exp ih =>
      change (a * b) * natPow (a * b) exp =
        (a * natPow a exp) * (b * natPow b exp)
      rw [ih]
      exact nat_mul_pair_swap a b (natPow a exp) (natPow b exp)

private theorem natPow_pos {base : Nat} :
    0 < base -> ∀ exp : Nat, 0 < natPow base exp
  | _basePos, 0 => Nat.succ_pos 0
  | basePos, exp + 1 => by
      change 0 < base * natPow base exp
      exact Nat.mul_pos basePos (natPow_pos basePos exp)

private theorem nat_add_mul_pred (x y : Nat) :
    0 < y -> x + x * (y - 1) = x * y := by
  intro yPos
  cases y with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 yPos)
  | succ y =>
      change x + x * y = x * Nat.succ y
      rw [Nat.mul_succ, Nat.add_comm]

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem natPrime_length_pos {p : BHist} :
    NatPrime p -> 0 < bwordLength p := by
  intro pPrime
  cases p with
  | Empty =>
      exact False.elim (NatUnaryStrictPrefix_empty_right_absurd pPrime.right.left)
  | e0 pTail =>
      cases pPrime.left
  | e1 pTail =>
      exact Nat.succ_pos _

def jordanTotientFactorsNat (k : Nat) : List BHist -> Nat
  | [] => 1
  | p :: ps =>
      if listContainsPrime p ps then
        natPow (bwordLength p) k * jordanTotientFactorsNat k ps
      else
        (natPow (bwordLength p) k - 1) * jordanTotientFactorsNat k ps

def jordanTotientFactors (k : Nat) (entries : List BHist) : BHist :=
  natToUnary (jordanTotientFactorsNat k entries)

def JordanTotientOfFactorization (k : Nat) (n value : BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ hsame value (jordanTotientFactors k entries)

theorem jordanTotientFactors_unary (k : Nat) (entries : List BHist) :
    UnaryHistory (jordanTotientFactors k entries) := by
  unfold jordanTotientFactors
  exact natToUnary_unary _

theorem jordanTotient_one_eq_eulerPhiFactorsNat (entries : List BHist) :
    jordanTotientFactorsNat 1 entries = eulerPhiFactorsNat entries := by
  induction entries with
  | nil =>
      rfl
  | cons p ps ih =>
      change
        (if listContainsPrime p ps then
          natPow (bwordLength p) 1 * jordanTotientFactorsNat 1 ps
        else
          (natPow (bwordLength p) 1 - 1) * jordanTotientFactorsNat 1 ps) =
        (if listContainsPrime p ps then
          bwordLength p * eulerPhiFactorsNat ps
        else
          (bwordLength p - 1) * eulerPhiFactorsNat ps)
      rw [natPow_one_exp, ih]

theorem jordanTotient_one_eq_eulerPhiFactors (entries : List BHist) :
    hsame (jordanTotientFactors 1 entries) (eulerPhiFactors entries) := by
  unfold jordanTotientFactors eulerPhiFactors
  rw [jordanTotient_one_eq_eulerPhiFactorsNat entries]
  exact hsame_refl _

theorem jordanTotient_one_eq_eulerPhi {n phi : BHist} :
    EulerPhiOfFactorization n phi -> JordanTotientOfFactorization 1 n phi := by
  intro phiData
  cases phiData with
  | intro entries data =>
      exact ⟨entries, data.left,
        hsame_trans data.right (hsame_symm (jordanTotient_one_eq_eulerPhiFactors entries))⟩

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

theorem jordanTotientFactorsNat_append_disjoint
    (k : Nat) (xs ys : List BHist) :
    listNoCommonPrime xs ys ->
      jordanTotientFactorsNat k (xs ++ ys) =
        jordanTotientFactorsNat k xs * jordanTotientFactorsNat k ys := by
  intro common
  induction xs with
  | nil =>
      change jordanTotientFactorsNat k ys = 1 * jordanTotientFactorsNat k ys
      rw [Nat.one_mul]
  | cons p ps ih =>
      unfold listNoCommonPrime at common
      change
        (if listContainsPrime p (ps ++ ys)
          then natPow (bwordLength p) k * jordanTotientFactorsNat k (ps ++ ys)
          else (natPow (bwordLength p) k - 1) *
            jordanTotientFactorsNat k (ps ++ ys)) =
        (if listContainsPrime p ps
          then natPow (bwordLength p) k * jordanTotientFactorsNat k ps
          else (natPow (bwordLength p) k - 1) *
            jordanTotientFactorsNat k ps) *
          jordanTotientFactorsNat k ys
      cases memPs : listContainsPrime p ps
      · have notAppend : listContainsPrime p (ps ++ ys) = false :=
          listContainsPrime_append_false_local ps ys memPs common.left
        rw [notAppend]
        change
          (natPow (bwordLength p) k - 1) * jordanTotientFactorsNat k (ps ++ ys) =
            ((natPow (bwordLength p) k - 1) * jordanTotientFactorsNat k ps) *
              jordanTotientFactorsNat k ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (natPow (bwordLength p) k - 1)
          (jordanTotientFactorsNat k ps) (jordanTotientFactorsNat k ys)).symm
      · have memAppend : listContainsPrime p (ps ++ ys) = true :=
          listContainsPrime_append_true_left_local ps ys memPs
        rw [memAppend]
        change
          natPow (bwordLength p) k * jordanTotientFactorsNat k (ps ++ ys) =
            (natPow (bwordLength p) k * jordanTotientFactorsNat k ps) *
              jordanTotientFactorsNat k ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (natPow (bwordLength p) k)
          (jordanTotientFactorsNat k ps) (jordanTotientFactorsNat k ys)).symm

theorem jordanTotient_factorization_product_multiplicative
    (k : Nat) {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          listNoCommonPrime xs ys ->
            JordanTotientOfFactorization k mn
              (natToUnary (jordanTotientFactorsNat k xs *
                jordanTotientFactorsNat k ys)) := by
  intro fx fy mul common
  have product : PrimeFactorizationProduct (xs ++ ys) mn :=
    PrimeFactorizationProduct_append_mul fx fy mul
  have appendValue :
      jordanTotientFactorsNat k (xs ++ ys) =
        jordanTotientFactorsNat k xs * jordanTotientFactorsNat k ys :=
    jordanTotientFactorsNat_append_disjoint k xs ys common
  exact ⟨xs ++ ys,
    ⟨NatMul_result_unary (PrimeFactorizationProduct_result_unary fx) mul, product⟩,
    by
      unfold jordanTotientFactors
      rw [appendValue]
      exact hsame_refl _⟩

theorem jordanTotient_factorization_product_multiplicative_of_gcd_one
    (k : Nat) {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          NatGcd m n NatOne ->
            JordanTotientOfFactorization k mn
              (natToUnary (jordanTotientFactorsNat k xs *
                jordanTotientFactorsNat k ys)) := by
  intro fx fy mul gcd
  exact jordanTotient_factorization_product_multiplicative k fx fy mul
    (PrimeFactorizationProduct_coprime_no_common fx fy gcd)

def jordanPrimePowerFactorNat (k : Nat) (p : BHist) : Nat -> Nat
  | 0 => 1
  | a + 1 =>
      natPow (bwordLength p) (k * a) *
        (natPow (bwordLength p) k - 1)

def jordanPrimePowerDivisorSumNat (k : Nat) (p : BHist) : Nat -> Nat
  | 0 => jordanPrimePowerFactorNat k p 0
  | a + 1 =>
      jordanPrimePowerDivisorSumNat k p a +
        jordanPrimePowerFactorNat k p (a + 1)

theorem jordanPrimePowerDivisorSumNat_eq_power
    (k : Nat) {p : BHist} :
    NatPrime p ->
      ∀ a : Nat,
        jordanPrimePowerDivisorSumNat k p a =
          natPow (bwordLength p) (k * a) := by
  intro pPrime
  have pLenPos : 0 < bwordLength p := natPrime_length_pos pPrime
  intro a
  induction a with
  | zero =>
      change 1 = natPow (bwordLength p) (k * 0)
      rw [Nat.mul_zero]
      rfl
  | succ a ih =>
      change
        jordanPrimePowerDivisorSumNat k p a +
            natPow (bwordLength p) (k * a) *
              (natPow (bwordLength p) k - 1) =
          natPow (bwordLength p) (k * Nat.succ a)
      rw [ih]
      have factorPositive : 0 < natPow (bwordLength p) k :=
        natPow_pos pLenPos k
      calc
        natPow (bwordLength p) (k * a) +
            natPow (bwordLength p) (k * a) *
              (natPow (bwordLength p) k - 1) =
            natPow (bwordLength p) (k * a) *
              natPow (bwordLength p) k :=
              nat_add_mul_pred (natPow (bwordLength p) (k * a))
                (natPow (bwordLength p) k) factorPositive
        _ = natPow (bwordLength p) (k * a + k) :=
            (natPow_add (bwordLength p) (k * a) k).symm
        _ = natPow (bwordLength p) (k * Nat.succ a) := by
            rw [Nat.mul_succ]

def jordanTotientProfileBlockNat (k : Nat) : PrimePowerProfile -> Nat
  | [] => 1
  | e :: es =>
      jordanPrimePowerFactorNat k e.prime e.exponent *
        jordanTotientProfileBlockNat k es

def jordanTotientProfileNat (k : Nat) (profile : PrimePowerProfile) : Nat :=
  jordanTotientProfileBlockNat k profile

def jordanTotientProfile (k : Nat) (profile : PrimePowerProfile) : BHist :=
  natToUnary (jordanTotientProfileNat k profile)

def jordanTotientProfileDivisorSumNat (k : Nat) : PrimePowerProfile -> Nat
  | [] => 1
  | e :: es =>
      jordanPrimePowerDivisorSumNat k e.prime e.exponent *
        jordanTotientProfileDivisorSumNat k es

def jordanTotientProfileDivisorSum
    (k : Nat) (profile : PrimePowerProfile) : BHist :=
  natToUnary (jordanTotientProfileDivisorSumNat k profile)

private theorem primeFlatProductNat_append (xs ys : List BHist) :
    primeFlatProductNat (xs ++ ys) =
      primeFlatProductNat xs * primeFlatProductNat ys := by
  induction xs with
  | nil =>
      change primeFlatProductNat ys = 1 * primeFlatProductNat ys
      rw [Nat.one_mul]
  | cons p ps ih =>
      change bwordLength p * primeFlatProductNat (ps ++ ys) =
        (bwordLength p * primeFlatProductNat ps) * primeFlatProductNat ys
      rw [ih]
      exact (nat_mul_assoc_pure (bwordLength p)
        (primeFlatProductNat ps) (primeFlatProductNat ys)).symm

private theorem primeFlatProductNat_expandPrimePower (p : BHist) :
    ∀ a : Nat,
      primeFlatProductNat (expandPrimePower p a) =
        natPow (bwordLength p) a
  | 0 => rfl
  | a + 1 => by
      change bwordLength p * primeFlatProductNat (expandPrimePower p a) =
        natPow (bwordLength p) (a + 1)
      rw [primeFlatProductNat_expandPrimePower p a]
      rfl

private theorem profile_block_power_eq_flat_power
    (k : Nat) :
    ∀ profile : PrimePowerProfile,
      ProfileValid profile ->
        jordanTotientProfileDivisorSumNat k profile =
          natPow (primeFlatProductNat (expandProfile profile)) k
  | [], _valid => by
      change 1 = natPow 1 k
      exact (natPow_one_base k).symm
  | e :: es, valid => by
      cases valid with
      | cons ePrime _eNonzero _absentTail validTail =>
          change
            jordanPrimePowerDivisorSumNat k e.prime e.exponent *
                jordanTotientProfileDivisorSumNat k es =
              natPow
                (primeFlatProductNat (expandPrimePower e.prime e.exponent ++
                  expandProfile es)) k
          have headSum :
              jordanPrimePowerDivisorSumNat k e.prime e.exponent =
                natPow (bwordLength e.prime) (k * e.exponent) :=
            jordanPrimePowerDivisorSumNat_eq_power k ePrime e.exponent
          have tailSum :
              jordanTotientProfileDivisorSumNat k es =
                natPow (primeFlatProductNat (expandProfile es)) k :=
            profile_block_power_eq_flat_power k es validTail
          rw [headSum, tailSum, primeFlatProductNat_append,
            primeFlatProductNat_expandPrimePower]
          calc
            natPow (bwordLength e.prime) (k * e.exponent) *
                natPow (primeFlatProductNat (expandProfile es)) k =
              natPow (natPow (bwordLength e.prime) e.exponent) k *
                natPow (primeFlatProductNat (expandProfile es)) k := by
                  rw [natPow_mul_right, Nat.mul_comm e.exponent k]
            _ =
              natPow
                (natPow (bwordLength e.prime) e.exponent *
                  primeFlatProductNat (expandProfile es)) k :=
                  (natPow_mul_base (natPow (bwordLength e.prime) e.exponent)
                    (primeFlatProductNat (expandProfile es)) k).symm

theorem jordanTotient_profile_divisor_sum_nat
    (k : Nat) {profile : PrimePowerProfile} :
    ProfileValid profile ->
      jordanTotientProfileDivisorSumNat k profile =
        natPow (primeFlatProductNat (expandProfile profile)) k := by
  exact profile_block_power_eq_flat_power k profile

theorem jordanTotient_divisor_sum_of_profile
    (k : Nat) {n : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile ->
      PrimeFactorization n (expandProfile profile) ->
        hsame (jordanTotientProfileDivisorSum k profile)
          (natToUnary (natPow (bwordLength n) k)) := by
  intro valid factorization
  have sumEq :
      jordanTotientProfileDivisorSumNat k profile =
        natPow (primeFlatProductNat (expandProfile profile)) k :=
    jordanTotient_profile_divisor_sum_nat k valid
  have productSame :
      hsame (primePowerProduct (expandProfile profile)) n :=
    primePowerProduct_eq_flat factorization.right
  have flatLength :
      primeFlatProductNat (expandProfile profile) = bwordLength n := by
    have lenEq := congrArg bwordLength productSame
    unfold primePowerProduct at lenEq
    rw [natToUnary_length, primePowerProductNat_eq_flat] at lenEq
    exact lenEq
  unfold jordanTotientProfileDivisorSum
  apply unary_hsame_of_length
  · exact natToUnary_unary _
  · exact natToUnary_unary _
  · rw [natToUnary_length, natToUnary_length]
    exact Eq.trans sumEq (congrArg (fun x => natPow x k) flatLength)

end BEDC.Derived.JordanTotientUp
