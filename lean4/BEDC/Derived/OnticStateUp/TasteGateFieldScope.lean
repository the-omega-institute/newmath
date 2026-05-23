import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def onticStateFields : OnticStateUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnticStateUp.mk S A K R H C P N => [S, A, K, R, H, C, P, N]

theorem OnticStateTasteGateFieldScope (x : OnticStateUp) :
    exists S A K R H C P N : BHist,
      x = OnticStateUp.mk S A K R H C P N /\
        onticStateFields x = [S, A, K, R, H, C, P, N] /\
          Cont H C (append H C) /\
            hsame (append S A) (append S A) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases x with
  | mk S A K R H C P N =>
      exact ⟨S, A, K, R, H, C, P, N, rfl, rfl, rfl, hsame_refl (append S A)⟩

end BEDC.Derived.OnticStateUp
