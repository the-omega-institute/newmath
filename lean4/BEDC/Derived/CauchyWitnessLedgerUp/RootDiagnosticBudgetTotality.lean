import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CauchyWitnessLedgerCarrier_root_diagnostic_budget_totality
    {Q B S K H C P N Q' B' S' K' H' C' P' N' endpoint : BHist} :
    FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q B S K H C P N) =
        FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q' B' S' K' H' C' P' N') →
      Cont Q B S →
        Cont S K endpoint →
          Cont Q' B' S' ∧ Cont S' K' endpoint := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields routeBudget routeEndpoint
  change [Q, B, S, K, H, C, P, N] = [Q', B', S', K', H', C', P', N'] at hfields
  injection hfields with hQ tailQ
  injection tailQ with hB tailB
  injection tailB with hS tailS
  injection tailS with hK _tailK
  subst hQ
  subst hB
  subst hS
  subst hK
  exact ⟨routeBudget, routeEndpoint⟩

end BEDC.Derived.CauchyWitnessLedgerUp
