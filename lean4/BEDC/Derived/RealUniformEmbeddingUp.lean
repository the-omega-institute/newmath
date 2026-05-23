import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RealUniformEmbeddingUp : Type where
  | mk : (S W D Q E U H C P N : BHist) -> RealUniformEmbeddingUp
  deriving DecidableEq

end BEDC.Derived
