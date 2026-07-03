import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived

inductive CauchyProductCompletionSealUp : Type where
  | mk (L R P B Q T S H C K N : BEDC.FKernel.Hist.BHist) : CauchyProductCompletionSealUp

end BEDC.Derived
