import BEDC.FKernel.Cont

namespace BEDC.Derived.GapClosureBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GapClosureBoundary_refusal_ledger_transport {G R H C P N G' R' : BHist}
    (hG : hsame G G') (route : Cont G C R) (route' : Cont G' C R') :
    hsame (append R (append H (append C (append P N))))
      (append R' (append H (append C (append P N)))) := by
  cases hG
  cases route
  cases route'
  rfl

end BEDC.Derived.GapClosureBoundaryUp
