import BEDC.Derived.PrimeUp.PrimeShape
import BEDC.Derived.PrimeUp.DividesClosure

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

inductive NatPrimeFactorization : List BHist -> BHist -> Prop where
  | unit : NatPrimeFactorization [] (BHist.e1 BHist.Empty)
  | singleton {p : BHist} : NatPrime p -> NatPrimeFactorization [p] p
  | cons {p q tail n : BHist} {ps : List BHist} :
      NatPrime p -> NatPrime q -> (hsame p q ∨ NatUnaryStrictPrefix p q) ->
        NatPrimeFactorization (q :: ps) tail -> NatMul p tail n ->
          NatPrimeFactorization (p :: q :: ps) n

inductive NatPrimeProduct : List BHist -> BHist -> Prop where
  | nil : NatPrimeProduct [] (BHist.e1 BHist.Empty)
  | cons {p psProduct n : BHist} {ps : List BHist} :
      NatPrime p -> NatPrimeProduct ps psProduct -> NatMul p psProduct n ->
        NatPrimeProduct (p :: ps) n

theorem NatPrimeProduct_result_not_empty {ps : List BHist} {n : BHist} :
    NatPrimeProduct ps n -> hsame n BHist.Empty -> False := by
  intro product
  induction product with
  | nil =>
      intro sameEmpty
      exact not_hsame_e1_empty sameEmpty
  | cons prime _product mul ih =>
      intro sameEmpty
      have primeShape := NatPrime_successor_tail_nonempty prime
      cases primeShape with
      | intro tail data =>
          exact NatMul_nonempty_factors_result_not_empty
            (fun pEmpty => not_hsame_e1_empty (data.left.symm.trans pEmpty)) ih mul sameEmpty

theorem NatPrimeFactorization_result_not_empty {ps : List BHist} {n : BHist} :
    NatPrimeFactorization ps n -> hsame n BHist.Empty -> False := by
  intro factorization
  induction factorization with
  | unit =>
      intro sameEmpty
      exact not_hsame_e1_empty sameEmpty
  | singleton prime =>
      intro sameEmpty
      exact NatPrime_empty_absurd prime sameEmpty
  | cons prime _nextPrime _ordered _tailFactorization mul tailNonempty =>
      intro sameEmpty
      have primeShape := NatPrime_successor_tail_nonempty prime
      cases primeShape with
      | intro tail data =>
          exact NatMul_nonempty_factors_result_not_empty
            (fun pEmpty => not_hsame_e1_empty (data.left.symm.trans pEmpty))
            tailNonempty mul sameEmpty

theorem NatPrimeProduct_result_unary {ps : List BHist} {n : BHist} :
    NatPrimeProduct ps n -> UnaryHistory n := by
  intro product
  induction product with
  | nil =>
      exact unary_e1_closed unary_empty
  | cons prime _tailProduct mul ih =>
      exact NatMul_result_unary prime.left mul

theorem NatPrimeProduct_cons_tail_divides {p n : BHist} {ps : List BHist} :
    NatPrimeProduct (p :: ps) n ->
      UnaryHistory p /\ exists tailProduct : BHist,
        NatPrimeProduct ps tailProduct /\ NatDivides tailProduct n := by
  intro product
  cases product with
  | cons prime tailProductProof mul =>
      have tailUnary : UnaryHistory _ := NatPrimeProduct_result_unary tailProductProof
      exact And.intro prime.left
        (Exists.intro _
          (And.intro tailProductProof
            (NatDivides_mul_right_closed prime.left tailUnary mul)))

theorem NatPrimeProduct_factor_mem_unary_divides_result {p n : BHist} {ps : List BHist} :
    p ∈ ps -> NatPrimeProduct ps n -> UnaryHistory p ∧ NatDivides p n := by
  intro member product
  induction product with
  | nil =>
      cases member
  | cons prime tailProductProof mul ih =>
      cases member with
      | head =>
          have tailUnary : UnaryHistory _ := NatPrimeProduct_result_unary tailProductProof
          exact And.intro prime.left (Exists.intro _ (And.intro tailUnary mul))
      | tail _ tailMember =>
          have tailData := ih tailMember
          exact And.intro tailData.left
            (NatDivides_mul_left_closed prime.left tailData.right mul)

end BEDC.Derived.PrimeUp
