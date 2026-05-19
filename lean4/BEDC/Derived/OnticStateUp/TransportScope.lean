import BEDC.Derived.OnticStateUp.TasteGate

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem OnticStateCarrier_transport_scope
    {S A K R H C P N observerRead residueRead transportRead auditRead : BHist} :
    Cont S A observerRead ->
      Cont A R residueRead ->
        Cont residueRead H transportRead ->
          Cont transportRead N auditRead ->
            FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N] ∧
              onticStateFromEventFlow (onticStateToEventFlow
                  (OnticStateUp.mk S A K R H C P N)) =
                some (OnticStateUp.mk S A K R H C P N) ∧
                hsame S S ∧ hsame A A ∧ hsame K K ∧ hsame R R ∧ hsame H H ∧
                  hsame C C ∧ hsame P P ∧ hsame N N ∧ Cont S A observerRead ∧
                    Cont A R residueRead ∧ Cont residueRead H transportRead ∧
                      Cont transportRead N auditRead := by
  -- BEDC touchpoint anchor: BHist FieldFaithful Cont hsame
  intro observerRoute residueRoute transportRoute auditRoute
  exact
    ⟨rfl,
      OnticStateTasteGate_single_carrier_alignment.right.left
        (OnticStateUp.mk S A K R H C P N),
      hsame_refl S, hsame_refl A, hsame_refl K, hsame_refl R, hsame_refl H,
      hsame_refl C, hsame_refl P, hsame_refl N, observerRoute, residueRoute,
      transportRoute, auditRoute⟩

end BEDC.Derived.OnticStateUp
