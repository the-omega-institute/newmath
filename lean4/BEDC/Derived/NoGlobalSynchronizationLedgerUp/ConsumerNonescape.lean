import BEDC.Derived.NoGlobalSynchronizationLedgerUp.TasteGate

namespace BEDC.Derived.NoGlobalSynchronizationLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem NoGlobalSynchronizationLedgerUp_consumer_nonescape
    {H0 H1 R B O I K S C P N localRead consumerRead namedRead : BHist} :
    Cont H0 H1 localRead →
      Cont localRead R consumerRead →
        Cont consumerRead N namedRead →
          FieldFaithful.fields
              (NoGlobalSynchronizationLedgerUp.mk H0 H1 R B O I K S C P N) =
            [H0, H1, R, B, O, I, K, S, C, P, N] ∧
            Cont H0 H1 localRead ∧ Cont localRead R consumerRead ∧
              Cont consumerRead N namedRead ∧ hsame R R ∧ hsame B B ∧ hsame K K := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful hsame
  intro localRoute consumerRoute namedRoute
  exact
    ⟨rfl, localRoute, consumerRoute, namedRoute, hsame_refl R, hsame_refl B,
      hsame_refl K⟩

end BEDC.Derived.NoGlobalSynchronizationLedgerUp
