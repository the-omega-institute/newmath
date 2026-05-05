import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.Derived.NatUp

inductive NatPrimeFactorization : List BHist -> BHist -> Prop where
  | unit : NatPrimeFactorization [] (BHist.e1 BHist.Empty)
  | singleton {p : BHist} : NatPrime p -> NatPrimeFactorization [p] p
  | cons {p q tail n : BHist} {ps : List BHist} :
      NatPrime p -> NatPrime q -> (hsame p q ∨ NatUnaryStrictPrefix p q) ->
        NatPrimeFactorization (q :: ps) tail -> NatMul p tail n ->
          NatPrimeFactorization (p :: q :: ps) n

end BEDC.Derived.PrimeUp
