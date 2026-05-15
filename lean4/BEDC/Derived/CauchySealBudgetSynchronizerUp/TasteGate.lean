import BEDC.Derived.CauchySealBudgetSynchronizerUp

namespace BEDC.Derived.CauchySealBudgetSynchronizerUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CauchySealBudgetSynchronizerTasteGate_obligation_surface
    (request sealRow budget tail selector compatibility transport route provenance nameCert :
      BHist) :
    cauchySealBudgetSynchronizerFields
        (CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector compatibility
          transport route provenance nameCert) =
      [request, sealRow, budget, tail, selector, compatibility, transport, route, provenance,
        nameCert] ∧
      cauchySealBudgetSynchronizerToEventFlow
          (CauchySealBudgetSynchronizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
        cauchySealBudgetSynchronizerToEventFlow
          (CauchySealBudgetSynchronizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · intro heq
    injection heq with _ hTail
    injection hTail with hRequest _
    cases hRequest

end BEDC.Derived.CauchySealBudgetSynchronizerUp
