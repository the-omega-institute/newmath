import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SamuelCompletionUp : Type where
  | mk
      (uniformEntourage cauchyFilter denseUniformEmbedding streamWindow regularReadback
        realSeal transport replay provenance name : BHist) :
      SamuelCompletionUp
  deriving DecidableEq

end BEDC.Derived
