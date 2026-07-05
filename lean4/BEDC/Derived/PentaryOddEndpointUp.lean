import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PentaryOddEndpointUp : Type where
  | mk (Q E H D M R B T C G N : BHist) : PentaryOddEndpointUp

end BEDC.Derived
