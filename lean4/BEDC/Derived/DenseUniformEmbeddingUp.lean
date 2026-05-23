import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DenseUniformEmbeddingUp : Type where
  | mk (S T I Q M E U H C P N : BHist) : DenseUniformEmbeddingUp
  deriving DecidableEq

end BEDC.Derived
