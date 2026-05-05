import BEDC.Derived.PrimeUp.PrimeShape

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

end BEDC.Derived.PrimeUp
