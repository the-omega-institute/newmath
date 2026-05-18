import BEDC.Derived.OnticStateUp.TasteGate

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem OnticStateSignatureStability {S A K R H C P N replay : BHist} :
    Cont S A replay →
      FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) = [S, A, K, R, H, C, P, N] ∧
        onticStateFromEventFlow (onticStateToEventFlow (OnticStateUp.mk S A K R H C P N)) =
          some (OnticStateUp.mk S A K R H C P N) ∧
          hsame S S ∧ hsame A A ∧ hsame K K ∧ hsame R R ∧ Cont S A replay := by
  -- BEDC touchpoint anchor: BHist FieldFaithful Cont hsame
  intro replayRoute
  exact
    ⟨rfl, OnticStateTasteGate_single_carrier_alignment.right.left
        (OnticStateUp.mk S A K R H C P N),
      hsame_refl S, hsame_refl A, hsame_refl K, hsame_refl R, replayRoute⟩

end BEDC.Derived.OnticStateUp
