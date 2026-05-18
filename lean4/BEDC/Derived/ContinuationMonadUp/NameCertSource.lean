import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

structure ContinuationMonadNameCertSource where
  A : BHist
  B : BHist
  C : BHist
  f : BHist
  g : BHist
  u : BHist
  H : BHist
  K : BHist
  L : BHist
  N : BHist
  carrier : ContinuationMonadCarrier A B C f g u H K L N
  routeWitness : Cont K u L
  endpointTransport : hsame N L

end BEDC.Derived.ContinuationMonadUp
