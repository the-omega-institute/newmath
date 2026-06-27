import BEDC.Derived.FermatLittleUp
import BEDC.Derived.PrimeUp.EmptyResult
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.PrimitiveRootFinal

namespace BEDC.Derived.PrattCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.EulerTheoremUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PrimitiveRootUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList (unaryPred)
open BEDC.Derived.ZModUp

abbrev NatOne : BHist := BHist.e1 BHist.Empty
abbrev NatTwo : BHist := BEDC.Derived.PrimitiveRootUp.NatTwo
abbrev NatThree : BHist := natToUnary 3
abbrev NatFour : BHist := BEDC.Derived.PrimitiveRootUp.NatFour
abbrev NatFive : BHist := BEDC.Derived.PrimitiveRootUp.NatFive

def primePred (n : BHist) : BHist :=
  unaryPred n

def LucasFactorWitness (n p : BHist) : Prop :=
  NatPrime p ∧ NatDivides p (primePred n)

structure LucasCertificate (n : BHist) where
  n_unary : UnaryHistory n
  n_nonempty : hsame n BHist.Empty -> False
  generator : ZMod n
  generator_nonzero : zmodNonzero generator
  prime_factors : List BHist
  factorization : PrimeFactorizationProduct prime_factors (primePred n)
  primitive_order :
    IsPrimitiveRoot n n_unary n_nonempty (primePred n) generator

inductive PrattCertificate : BHist -> Prop where
  | two : PrattCertificate NatTwo
  | lucas {n : BHist} :
      (lucas : LucasCertificate n) ->
      (subcerts : ∀ p : BHist, p ∈ lucas.prime_factors -> PrattCertificate p) ->
        PrattCertificate n

theorem lucas_certificate_fermat_power {n : BHist} (cert : LucasCertificate n) :
    PowerOneAtNat n cert.n_unary cert.n_nonempty cert.generator
      (bwordLength (primePred n)) := by
  exact cert.primitive_order.pow_one

theorem primeFactorizationProduct_factor_prime :
    ∀ {ps : List BHist} {n p : BHist},
      PrimeFactorizationProduct ps n -> p ∈ ps -> NatPrime p
  | [], _n, _p, _product, mem => by
      cases mem
  | q :: qs, _n, p, product, mem => by
      cases product with
      | intro qPrime tailData =>
          cases mem with
          | head =>
              exact qPrime
          | tail _ tailMem =>
              cases tailData with
              | intro tailProduct tailProductData =>
                  exact primeFactorizationProduct_factor_prime
                    tailProductData.left tailMem

theorem primeFactorizationProduct_factor_divides :
    ∀ {ps : List BHist} {n p : BHist},
      PrimeFactorizationProduct ps n -> p ∈ ps -> NatDivides p n
  | [], _n, _p, _product, mem => by
      cases mem
  | q :: qs, n, p, product, mem => by
      cases product with
      | intro qPrime tailData =>
          cases tailData with
          | intro tailProduct tailProductData =>
              cases mem with
              | head =>
                  exact ⟨tailProduct, NatMul_right_unary tailProductData.right,
                    tailProductData.right⟩
              | tail _ tailMem =>
                  have tailDivides :
                      NatDivides p tailProduct :=
                    primeFactorizationProduct_factor_divides
                      tailProductData.left tailMem
                  exact NatDivides_mul_left_closed
                    qPrime.left tailDivides tailProductData.right

theorem lucas_certificate_factor_prime {n p : BHist}
    (cert : LucasCertificate n) :
    p ∈ cert.prime_factors -> NatPrime p := by
  intro mem
  exact primeFactorizationProduct_factor_prime cert.factorization mem

theorem lucas_certificate_factor_divides_predecessor {n p : BHist}
    (cert : LucasCertificate n) :
    p ∈ cert.prime_factors -> NatDivides p (primePred n) := by
  intro mem
  exact primeFactorizationProduct_factor_divides cert.factorization mem

theorem lucas_certificate_factor_witness {n p : BHist}
    (cert : LucasCertificate n) :
    p ∈ cert.prime_factors -> LucasFactorWitness n p := by
  intro mem
  exact ⟨lucas_certificate_factor_prime cert mem,
    lucas_certificate_factor_divides_predecessor cert mem⟩

private theorem unary_nonempty_length_positive {h : BHist} :
    UnaryHistory h -> (h = BHist.Empty -> False) -> 0 < bwordLength h := by
  intro hUnary hNonempty
  cases h with
  | Empty =>
      exact False.elim (hNonempty rfl)
  | e0 _tail =>
      cases hUnary
  | e1 tail =>
      change 0 < Nat.succ (bwordLength tail)
      exact Nat.succ_pos (bwordLength tail)

theorem lucas_certificate_factor_cofactor_power_not_one {n p : BHist}
    (cert : LucasCertificate n) (mem : p ∈ cert.prime_factors) :
    ∃ cofactor : BHist,
      UnaryHistory cofactor ∧
        NatMul p cofactor (primePred n) ∧
          (PowerOneAtNat n cert.n_unary cert.n_nonempty cert.generator
              (bwordLength cofactor) -> False) := by
  have factorPrime : NatPrime p :=
    lucas_certificate_factor_prime cert mem
  have extracted :=
    factorization_extract_mem factorPrime cert.factorization
      ⟨p, mem, hsame_refl p⟩
  cases extracted with
  | intro rest extractedRest =>
      cases extractedRest with
      | intro cofactor extractedData =>
          have cofactorUnary : UnaryHistory cofactor :=
            PrimeFactorizationProduct_result_unary extractedData.right.left
          have cofactorNonemptyHsame : hsame cofactor BHist.Empty -> False := by
            intro cofactorEmpty
            have predEmpty : hsame (primePred n) BHist.Empty :=
              (NatMul_empty_result_iff_factor_empty_or_multiplier_empty
                extractedData.right.right).mpr (Or.inr cofactorEmpty)
            exact PrimeFactorizationProduct_result_not_empty cert.factorization predEmpty
          have cofactorNonempty : cofactor = BHist.Empty -> False := by
            intro cofactorEmpty
            exact cofactorNonemptyHsame cofactorEmpty
          have cofactorPositive : 0 < bwordLength cofactor :=
            unary_nonempty_length_positive cofactorUnary cofactorNonempty
          have cofactorLt : bwordLength cofactor < bwordLength (primePred n) := by
            have oneLtP : 1 < bwordLength p :=
              NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty)
                factorPrime.right.left
            have productLength :
                bwordLength (primePred n) =
                  bwordLength p * bwordLength cofactor :=
              NatMul_bwordLength extractedData.right.right
            have raw :
                1 * bwordLength cofactor <
                  bwordLength p * bwordLength cofactor :=
              Nat.mul_lt_mul_of_pos_right oneLtP cofactorPositive
            rw [Nat.one_mul] at raw
            exact Nat.lt_of_lt_of_eq raw productLength.symm
          exact
            ⟨cofactor, cofactorUnary, extractedData.right.right,
              fun powOne =>
                cert.primitive_order.minimal
                  (bwordLength cofactor) cofactorPositive cofactorLt powOne⟩

theorem pratt_certificate_two_prime :
    NatPrime NatTwo := by
  change NatPrime (BHist.e1 (BHist.e1 BHist.Empty))
  exact NatPrime_first_pair.left

theorem pratt_certificate_three_prime :
    NatPrime NatThree := by
  change NatPrime (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty)))
  exact NatPrime_first_pair.right

theorem pratt_certificate_five_prime :
    NatPrime NatFive := by
  have large : NatUnaryStrictPrefix NatOne NatFive := by
    refine ⟨NatFour, natToUnary_unary 4, ?_, ?_⟩
    · intro empty
      unfold NatFour natToUnary at empty
      cases empty
    · unfold NatOne NatFour NatFive natToUnary
      exact BEDC.FKernel.Cont.cont_intro rfl
  change NatPrime (minFactor NatFive large)
  exact minFactor_prime large

theorem two_pred_factorization :
    PrimeFactorizationProduct [] (primePred NatTwo) := by
  unfold primePred NatTwo natToUnary unaryPred
  rfl

theorem three_pred_factorization :
    PrimeFactorizationProduct [NatTwo] (primePred NatThree) := by
  unfold primePred NatThree natToUnary unaryPred
  exact ⟨pratt_certificate_two_prime, NatOne, rfl,
    (NatMul_unit_right_iff pratt_certificate_two_prime.left).mpr
      (hsame_refl NatTwo)⟩

def twoModThree : ZMod NatThree :=
  zmodFromNat NatThree (natToUnary_unary 3)
    (fun empty => by
      unfold NatThree natToUnary at empty
      cases empty)
    NatTwo (natToUnary_unary 2)

private theorem two_mod_three_not_pow_one_at_one :
    PowerOneAtNat NatThree (natToUnary_unary 3)
      (fun empty => by
        unfold NatThree natToUnary at empty
        cases empty)
      twoModThree 1 -> False := by
  intro pow
  unfold PowerOneAtNat zmodPowByNat twoModThree zmodFromNat zmodOne zmodEq at pow
  unfold NatThree NatTwo BEDC.Derived.PadicUp.NatOne natToUnary natMulFn natModFn at pow
  cases pow

private theorem two_mod_three_minimal :
    ∀ j : Nat, 0 < j -> j < bwordLength NatTwo ->
      PowerOneAtNat NatThree (natToUnary_unary 3)
        (fun empty => by
          unfold NatThree natToUnary at empty
          cases empty)
        twoModThree j -> False := by
  intro j jPositive jLt pow
  cases j with
  | zero =>
      exact Nat.not_lt_zero 0 jPositive
  | succ j1 =>
      cases j1 with
      | zero =>
          exact two_mod_three_not_pow_one_at_one pow
      | succ j2 =>
          change Nat.succ (Nat.succ j2) < 2 at jLt
          have ltOne : Nat.succ j2 < 1 := Nat.succ_lt_succ_iff.mp jLt
          have ltZero : j2 < 0 := Nat.succ_lt_succ_iff.mp ltOne
          exact Nat.not_lt_zero j2 ltZero

theorem two_mod_three_has_order_two :
    HasMultOrder NatThree (natToUnary_unary 3)
      (fun empty => by
        unfold NatThree natToUnary at empty
        cases empty)
      twoModThree NatTwo where
  k_unary := natToUnary_unary 2
  k_positive := by
    change 0 < 2
    exact Nat.succ_pos 1
  pow_one := by
    unfold PowerOneAtNat zmodPowByNat twoModThree zmodFromNat zmodOne zmodEq
    unfold NatThree NatTwo BEDC.Derived.PadicUp.NatOne natToUnary natMulFn natModFn
    rfl
  minimal := two_mod_three_minimal

theorem two_mod_three_is_primitive_root :
    IsPrimitiveRoot NatThree (natToUnary_unary 3)
      (fun empty => by
        unfold NatThree natToUnary at empty
        cases empty)
      NatTwo twoModThree :=
  two_mod_three_has_order_two

def NatThree_lucas_certificate : LucasCertificate NatThree where
  n_unary := natToUnary_unary 3
  n_nonempty := by
    intro empty
    unfold NatThree natToUnary at empty
    cases empty
  generator := twoModThree
  generator_nonzero := by
    unfold twoModThree zmodFromNat zmodNonzero
    intro empty
    unfold NatThree NatTwo natToUnary natModFn at empty
    cases empty
  prime_factors := [NatTwo]
  factorization := three_pred_factorization
  primitive_order := two_mod_three_is_primitive_root

def NatTwo_pratt_certificate : PrattCertificate NatTwo :=
  PrattCertificate.two

def NatThree_pratt_certificate : PrattCertificate NatThree :=
  PrattCertificate.lucas NatThree_lucas_certificate
    (fun p mem => by
      cases mem with
      | head =>
          exact NatTwo_pratt_certificate
      | tail _ tailMem =>
          cases tailMem)

theorem five_pred_factorization :
    PrimeFactorizationProduct [NatTwo, NatTwo] (primePred NatFive) := by
  unfold primePred NatFive NatTwo natToUnary unaryPred
  refine ⟨pratt_certificate_two_prime, BHist.e1 (BHist.e1 BHist.Empty), ?_, ?_⟩
  · exact ⟨pratt_certificate_two_prime, NatOne, rfl,
      (NatMul_unit_right_iff pratt_certificate_two_prime.left).mpr
        (hsame_refl (BHist.e1 (BHist.e1 BHist.Empty)))⟩
  · exact NatMul.succ
      (NatMul.succ (NatMul.zero (unary_e1_closed (unary_e1_closed unary_empty)))
        (cont_intro rfl))
      (cont_intro rfl)

def NatFive_lucas_certificate : LucasCertificate NatFive where
  n_unary := natToUnary_unary 5
  n_nonempty := by
    intro empty
    unfold NatFive natToUnary at empty
    cases empty
  generator := BEDC.Derived.PrimitiveRootUp.twoModFive
  generator_nonzero := by
    unfold BEDC.Derived.PrimitiveRootUp.twoModFive zmodFromNat zmodNonzero
    intro empty
    unfold BEDC.Derived.PrimitiveRootUp.NatFive BEDC.Derived.PrimitiveRootUp.NatTwo
      natToUnary natModFn at empty
    cases empty
  prime_factors := [NatTwo, NatTwo]
  factorization := five_pred_factorization
  primitive_order := BEDC.Derived.PrimitiveRootUp.two_mod_five_is_primitive_root

def NatFive_pratt_certificate : PrattCertificate NatFive :=
  PrattCertificate.lucas NatFive_lucas_certificate
    (fun p mem => by
      cases mem with
      | head =>
          exact NatTwo_pratt_certificate
      | tail _ tailMem =>
          cases tailMem with
          | head =>
              exact NatTwo_pratt_certificate
          | tail _ tailTailMem =>
              cases tailTailMem)

theorem NatTwo_pratt_certificate_prime :
    NatPrime NatTwo :=
  pratt_certificate_two_prime

theorem NatThree_pratt_certificate_prime :
    NatPrime NatThree :=
  pratt_certificate_three_prime

theorem NatFive_pratt_certificate_prime :
    NatPrime NatFive :=
  pratt_certificate_five_prime

end BEDC.Derived.PrattCertificateUp
