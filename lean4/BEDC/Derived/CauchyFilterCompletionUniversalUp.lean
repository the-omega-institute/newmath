import BEDC.FKernel.Unary.History

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyFilterCompletionUniversalUp : Type where
  | mk :
      (sourceFilter denseEmbedding completionTarget sourceMap factorMap uniquenessLedger
        universalTransport transport replay provenance localName : BHist) ->
      CauchyFilterCompletionUniversalUp

end BEDC.Derived
