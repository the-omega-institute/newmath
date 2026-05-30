import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformEmbeddingUp : Type where
  | mk (S T I U J R H C P N : BHist) : UniformEmbeddingUp
  deriving DecidableEq

end BEDC.Derived
