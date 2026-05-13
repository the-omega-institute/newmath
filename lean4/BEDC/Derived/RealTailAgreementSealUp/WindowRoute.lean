import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.RealTailAgreementSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def RealTailAgreementSealWindowRoute (W D A result : BHist) : Prop :=
  ∃ readback : BHist, Cont W D readback ∧ Cont readback A result

theorem RealTailAgreementSealWindowRoute_result_exact {W D A result : BHist}
    (route : RealTailAgreementSealWindowRoute W D A result) :
    hsame result (append W (append D A)) := by
  -- BEDC touchpoint anchor: BHist Cont
  cases route with
  | intro readback routeData =>
      cases routeData with
      | intro first second =>
          cases first
          cases second
          exact append_assoc W D A

theorem RealTailAgreementSealWindowRoute_result_deterministic {W D A r s : BHist}
    (left : RealTailAgreementSealWindowRoute W D A r)
    (right : RealTailAgreementSealWindowRoute W D A s) :
    hsame r s ∧ hsame r (append W (append D A)) ∧
      hsame s (append W (append D A)) := by
  -- BEDC touchpoint anchor: BHist Cont
  have hr : hsame r (append W (append D A)) :=
    RealTailAgreementSealWindowRoute_result_exact left
  have hs : hsame s (append W (append D A)) :=
    RealTailAgreementSealWindowRoute_result_exact right
  constructor
  · exact Eq.trans hr hs.symm
  · constructor
    · exact hr
    · exact hs

end BEDC.Derived.RealTailAgreementSealUp
