import BEDC.FKernel.Unary.History

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopSeparatedRealCompletionUp : Type where
  | mk :
      (stream regular metricCompletion separatedReflection realSeal transport replay provenance
        localName : BHist) ->
      BishopSeparatedRealCompletionUp

end BEDC.Derived
