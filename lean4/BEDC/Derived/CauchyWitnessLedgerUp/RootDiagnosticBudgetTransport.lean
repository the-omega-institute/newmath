import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CauchyWitnessLedgerCarrier_root_diagnostic_budget_transport
    {Q B S K H C P N Q' B' S' K' H' C' P' N' endpoint terminal : BHist} :
    FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q B S K H C P N) =
        FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q' B' S' K' H' C' P' N') →
      Cont Q B S →
        Cont S K endpoint →
          Cont endpoint C terminal →
            K = K' ∧ H = H' ∧ C = C' ∧ Cont Q' B' S' ∧
              Cont S' K' endpoint ∧ Cont endpoint C' terminal := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields routeBudget routeEndpoint routeTerminal
  change [Q, B, S, K, H, C, P, N] = [Q', B', S', K', H', C', P', N'] at hfields
  injection hfields with hQ tailQ
  injection tailQ with hB tailB
  injection tailB with hS tailS
  injection tailS with hK tailK
  injection tailK with hH tailH
  injection tailH with hC _tailC
  subst hQ
  subst hB
  subst hS
  subst hK
  subst hH
  subst hC
  exact ⟨rfl, rfl, rfl, routeBudget, routeEndpoint, routeTerminal⟩

end BEDC.Derived.CauchyWitnessLedgerUp
