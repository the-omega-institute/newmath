import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

inductive MalformedRealSealedDenom : BHist -> Prop where
  | sealed_empty {h : BHist} :
      hsame h (BHist.e1 BHist.Empty) -> MalformedRealSealedDenom h
  | sealed_inner_e0 {h t : BHist} :
      hsame h (BHist.e1 (BHist.e0 t)) -> MalformedRealSealedDenom h
  | sealed_append_e0 {h p z : BHist} :
      hsame h (BHist.e1 (append p (BHist.e0 z))) -> MalformedRealSealedDenom h

end BEDC.Derived.RealUp
