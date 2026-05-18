import BEDC.Derived.OnticStateUp.TasteGate

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem OnticStateComponentwiseTransportScope
    {S A K R H C P N observerRead residueRead auditRead : BHist} :
    Cont S A observerRead →
      Cont A R residueRead →
        Cont residueRead N auditRead →
          FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
              [S, A, K, R, H, C, P, N] ∧
            onticStateFromEventFlow (onticStateToEventFlow
                (OnticStateUp.mk S A K R H C P N)) =
              some (OnticStateUp.mk S A K R H C P N) ∧
              hsame S S ∧ hsame A A ∧ hsame R R ∧ hsame N N ∧
                Cont S A observerRead ∧ Cont A R residueRead ∧
                  Cont residueRead N auditRead := by
  -- BEDC touchpoint anchor: BHist FieldFaithful Cont hsame
  intro observerRoute residueRoute auditRoute
  exact
    ⟨rfl,
      OnticStateTasteGate_single_carrier_alignment.right.left
        (OnticStateUp.mk S A K R H C P N),
      hsame_refl S, hsame_refl A, hsame_refl R, hsame_refl N,
      observerRoute, residueRoute, auditRoute⟩

end BEDC.Derived.OnticStateUp
