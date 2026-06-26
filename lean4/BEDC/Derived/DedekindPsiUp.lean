import BEDC.Derived.ArithmeticFnUp

namespace BEDC.Derived.DedekindPsiUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.GcdUp

def dedekindPsiFactorsNat : List BHist -> Nat
  | [] => 1
  | p :: ps =>
      if listContainsPrime p ps then bwordLength p * dedekindPsiFactorsNat ps
      else (bwordLength p + 1) * dedekindPsiFactorsNat ps

def dedekindPsiFactors (entries : List BHist) : BHist :=
  natToUnary (dedekindPsiFactorsNat entries)

def DedekindPsiOfFactorization (n psi : BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ hsame psi (dedekindPsiFactors entries)

def psi (n psiValue : BHist) : Prop :=
  DedekindPsiOfFactorization n psiValue

theorem dedekindPsiFactors_unary (entries : List BHist) :
    UnaryHistory (dedekindPsiFactors entries) := by
  unfold dedekindPsiFactors
  exact natToUnary_unary _

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

private theorem listContainsPrime_append_true_left {p : BHist} :
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

private theorem listContainsPrime_append_false {p : BHist} :
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

theorem dedekindPsiFactorsNat_append_disjoint
    (xs ys : List BHist) :
    listNoCommonPrime xs ys ->
      dedekindPsiFactorsNat (xs ++ ys) =
        dedekindPsiFactorsNat xs * dedekindPsiFactorsNat ys := by
  intro common
  induction xs with
  | nil =>
      change dedekindPsiFactorsNat ys = 1 * dedekindPsiFactorsNat ys
      rw [Nat.one_mul]
  | cons p ps ih =>
      unfold listNoCommonPrime at common
      change
        (if listContainsPrime p (ps ++ ys)
          then bwordLength p * dedekindPsiFactorsNat (ps ++ ys)
          else (bwordLength p + 1) * dedekindPsiFactorsNat (ps ++ ys)) =
            (if listContainsPrime p ps
              then bwordLength p * dedekindPsiFactorsNat ps
              else (bwordLength p + 1) * dedekindPsiFactorsNat ps) *
                dedekindPsiFactorsNat ys
      cases memPs : listContainsPrime p ps
      · have notAppend : listContainsPrime p (ps ++ ys) = false :=
          listContainsPrime_append_false ps ys memPs common.left
        rw [notAppend]
        change
          (bwordLength p + 1) * dedekindPsiFactorsNat (ps ++ ys) =
            ((bwordLength p + 1) * dedekindPsiFactorsNat ps) *
              dedekindPsiFactorsNat ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (bwordLength p + 1)
          (dedekindPsiFactorsNat ps) (dedekindPsiFactorsNat ys)).symm
      · have memAppend : listContainsPrime p (ps ++ ys) = true :=
          listContainsPrime_append_true_left ps ys memPs
        rw [memAppend]
        change
          bwordLength p * dedekindPsiFactorsNat (ps ++ ys) =
            (bwordLength p * dedekindPsiFactorsNat ps) *
              dedekindPsiFactorsNat ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (bwordLength p)
          (dedekindPsiFactorsNat ps) (dedekindPsiFactorsNat ys)).symm

theorem dedekindPsiFactors_append_disjoint_hsame
    (xs ys : List BHist) :
    listNoCommonPrime xs ys ->
      hsame (dedekindPsiFactors (xs ++ ys))
        (natToUnary (dedekindPsiFactorsNat xs * dedekindPsiFactorsNat ys)) := by
  intro common
  unfold dedekindPsiFactors
  exact congrArg natToUnary (dedekindPsiFactorsNat_append_disjoint xs ys common)

private theorem repeatPrimeFactor_contains_self
    (p : BHist) :
    ∀ k : Nat, listContainsPrime p (repeatPrimeFactor p (k + 1)) = true
  | 0 => by
      change (if p = p then true else false) = true
      rw [if_pos rfl]
  | k + 1 => by
      change (if p = p then true else listContainsPrime p (repeatPrimeFactor p (k + 1))) = true
      rw [if_pos rfl]

private theorem natPow_mul_succ_add_one (a k : Nat) :
    natPow a k * (a + 1) = natPow a (k + 1) + natPow a k := by
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (natPow a k) a]
  rfl

theorem dedekindPsi_prime_power_product_nat
    (p : BHist) :
    ∀ k : Nat,
      dedekindPsiFactorsNat (repeatPrimeFactor p (k + 1)) =
        natPow (bwordLength p) k * (bwordLength p + 1)
  | 0 => by
      change
        (if listContainsPrime p ([] : List BHist) = true
          then bwordLength p * 1
          else (bwordLength p + 1) * 1) =
            1 * (bwordLength p + 1)
      rw [if_neg (by intro impossible; cases impossible)]
      rw [Nat.mul_one, Nat.one_mul]
  | k + 1 => by
      change
        (if listContainsPrime p (repeatPrimeFactor p (k + 1)) = true
          then bwordLength p *
            dedekindPsiFactorsNat (repeatPrimeFactor p (k + 1))
          else (bwordLength p + 1) *
            dedekindPsiFactorsNat (repeatPrimeFactor p (k + 1))) =
            natPow (bwordLength p) (k + 1) * (bwordLength p + 1)
      rw [repeatPrimeFactor_contains_self p k]
      rw [if_pos rfl]
      rw [dedekindPsi_prime_power_product_nat p k]
      exact (nat_mul_assoc_pure (bwordLength p) (natPow (bwordLength p) k)
        (bwordLength p + 1)).symm

theorem dedekindPsi_prime_power_sum_nat
    (p : BHist) (k : Nat) :
    dedekindPsiFactorsNat (repeatPrimeFactor p (k + 1)) =
      natPow (bwordLength p) (k + 1) + natPow (bwordLength p) k := by
  rw [dedekindPsi_prime_power_product_nat p k]
  exact natPow_mul_succ_add_one (bwordLength p) k

theorem dedekindPsi_prime_power_sum_hsame
    (p : BHist) (k : Nat) :
    hsame
      (dedekindPsiFactors (repeatPrimeFactor p (k + 1)))
      (natToUnary
        (natPow (bwordLength p) (k + 1) + natPow (bwordLength p) k)) := by
  unfold dedekindPsiFactors
  exact congrArg natToUnary (dedekindPsi_prime_power_sum_nat p k)

theorem dedekindPsi_prime_power_of_factorization
    {p power psiValue : BHist} {k : Nat} :
    PrimeFactorizationProduct (repeatPrimeFactor p (k + 1)) power ->
      hsame psiValue
        (natToUnary
          (natPow (bwordLength p) (k + 1) + natPow (bwordLength p) k)) ->
        DedekindPsiOfFactorization power psiValue := by
  intro product displayed
  exact ⟨repeatPrimeFactor p (k + 1),
    ⟨PrimeFactorizationProduct_result_unary product, product⟩,
    hsame_trans displayed
      (hsame_symm (dedekindPsi_prime_power_sum_hsame p k))⟩

theorem dedekindPsi_factorization_product_multiplicative
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          listNoCommonPrime xs ys ->
            DedekindPsiOfFactorization mn
              (natToUnary
                (dedekindPsiFactorsNat xs * dedekindPsiFactorsNat ys)) := by
  intro fx fy mul common
  have product : PrimeFactorizationProduct (xs ++ ys) mn :=
    PrimeFactorizationProduct_append_mul fx fy mul
  exact ⟨xs ++ ys,
    ⟨NatMul_result_unary (PrimeFactorizationProduct_result_unary fx) mul, product⟩,
    hsame_symm (dedekindPsiFactors_append_disjoint_hsame xs ys common)⟩

theorem dedekindPsi_factorization_product_multiplicative_of_gcd_one
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          NatGcd m n BEDC.Derived.PadicUp.NatOne ->
            DedekindPsiOfFactorization mn
              (natToUnary
                (dedekindPsiFactorsNat xs * dedekindPsiFactorsNat ys)) := by
  intro fx fy mul gcd
  exact dedekindPsi_factorization_product_multiplicative fx fy mul
    (PrimeFactorizationProduct_coprime_no_common fx fy gcd)

end BEDC.Derived.DedekindPsiUp
