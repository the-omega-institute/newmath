import BEDC.Derived.PrimeUp

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

end BEDC.Derived.PrimeUp
