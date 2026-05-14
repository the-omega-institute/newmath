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

theorem RealTailAgreementSeal_left_right_threshold_synchrony
    {R S W D A H C P N leftRead rightRead leftDyadic rightDyadic : BHist} :
    Cont R W leftRead →
      Cont S W rightRead →
        Cont leftRead D leftDyadic →
          Cont rightRead D rightDyadic →
            hsame leftDyadic (append (append R W) D) ∧
              hsame rightDyadic (append (append S W) D) ∧
                Cont R W leftRead ∧ Cont S W rightRead := by
  -- BEDC touchpoint anchor: BHist Cont
  intro leftWindow rightWindow leftReadback rightReadback
  constructor
  · cases leftWindow
    cases leftReadback
    rfl
  · constructor
    · cases rightWindow
      cases rightReadback
      rfl
    · constructor
      · exact leftWindow
      · exact rightWindow

end BEDC.Derived.RealTailAgreementSealUp
