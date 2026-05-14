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
      BHistCarrier.toEventFlow
          (CauchySealBudgetSynchronizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
        BHistCarrier.toEventFlow
          (CauchySealBudgetSynchronizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · exact
      ChapterTasteGate.layer_separation
        (CauchySealBudgetSynchronizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
        (CauchySealBudgetSynchronizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty)
        (by
          intro h
          cases h)

end BEDC.Derived.CauchySealBudgetSynchronizerUp
