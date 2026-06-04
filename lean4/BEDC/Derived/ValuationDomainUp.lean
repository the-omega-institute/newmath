import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ValuationDomainUp : Type where
  | mk
      (ring fractionField idealChain localField fractionBoundary transport replay provenance name :
        BHist) :
      ValuationDomainUp
  deriving DecidableEq

def valuationDomainRows : ValuationDomainUp -> List BHist
  | ValuationDomainUp.mk R F I L Q H C P N => [R, F, I, L, Q, H, C, P, N]

end BEDC.Derived
