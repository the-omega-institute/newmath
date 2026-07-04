import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive AssouadSnowflakeEmbeddingUp : Type where
  | mk (M D A S E B Q R H C P N : BHist) : AssouadSnowflakeEmbeddingUp

end BEDC.Derived
