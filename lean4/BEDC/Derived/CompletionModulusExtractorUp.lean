import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompletionModulusExtractorUp : Type where
  | mk
      (metricCompletion cauchyFilterBasis streamWindow regularReadback dyadicTolerance
        extractedModulus realSeal transport replay provenance localName : BHist) :
      CompletionModulusExtractorUp
  deriving DecidableEq

end BEDC.Derived
