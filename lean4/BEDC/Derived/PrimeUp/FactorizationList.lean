import BEDC.Derived.PrimeUp.NatMulTransport
import BEDC.Derived.PrimeUp.PrimeShape

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def PrimeFactorizationProduct : List BHist -> BHist -> Prop
  | [], n => hsame n (BHist.e1 BHist.Empty)
  | p :: ps, n =>
      NatPrime p ∧ ∃ tailProduct : BHist,
        PrimeFactorizationProduct ps tailProduct ∧ NatMul p tailProduct n

def PrimeFactorization (n : BHist) (factors : List BHist) : Prop :=
  UnaryHistory n ∧ PrimeFactorizationProduct factors n

theorem PrimeFactorization_cons_head_divides {p n : BHist} {ps : List BHist} :
    PrimeFactorization n (p :: ps) -> NatPrime p ∧ NatDivides p n := by
  intro factorization
  cases factorization with
  | intro _nUnary product =>
      cases product with
      | intro pPrime productTail =>
          constructor
          · exact pPrime
          · cases productTail with
            | intro tailProduct tailData =>
                exact Exists.intro tailProduct
                  (And.intro (NatMul_right_unary tailData.right) tailData.right)

theorem PrimeFactorizationProduct_result_hsame_transport {ps : List BHist} {n n' : BHist} :
    PrimeFactorizationProduct ps n -> hsame n n' -> PrimeFactorizationProduct ps n' := by
  intro product sameResult
  cases ps with
  | nil =>
      exact hsame_trans (hsame_symm sameResult) product
  | cons p ps =>
      cases product with
      | intro pPrime productTail =>
          cases productTail with
          | intro tailProduct tailData =>
              exact And.intro pPrime
                (Exists.intro tailProduct
                  (And.intro tailData.left
                    (NatMul_result_hsame_transport tailData.right sameResult).right))

theorem PrimeFactorizationProduct_result_not_empty {ps : List BHist} {n : BHist} :
    PrimeFactorizationProduct ps n -> hsame n BHist.Empty -> False := by
  intro product
  induction ps generalizing n with
  | nil =>
      intro sameEmpty
      exact not_hsame_e1_empty (hsame_trans (hsame_symm product) sameEmpty)
  | cons p ps ih =>
      intro sameEmpty
      cases product with
      | intro pPrime tailData =>
          cases tailData with
          | intro tailProduct productTail =>
              exact NatMul_nonempty_factors_result_not_empty
                (NatPrime_empty_absurd pPrime)
                (fun tailEmpty => ih productTail.left tailEmpty)
                productTail.right sameEmpty

end BEDC.Derived.PrimeUp
