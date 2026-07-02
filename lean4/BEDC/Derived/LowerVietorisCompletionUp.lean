import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LowerVietorisCompletionUp : Type where
  | mk
      (topology lowerTopology vietorisTopology cauchyIdeal finiteLowerHits
        directedStability completionHandoff transport replay provenance localNameCert : BHist) :
      LowerVietorisCompletionUp
  deriving DecidableEq

end BEDC.Derived
