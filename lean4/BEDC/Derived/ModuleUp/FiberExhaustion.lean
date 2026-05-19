import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist

theorem ModuleSingletonSmul_fiber_exhaustion {r m o o' : BHist} :
    ModuleSingletonCarrier r -> ModuleSingletonCarrier m ->
      ModuleSingletonClassifier (ModuleSingletonSmul r m) o ->
        ModuleSingletonClassifier (ModuleSingletonSmul r m) o' ->
          (ModuleSingletonCarrier o ∧ ModuleSingletonCarrier o' ∧
            hsame (ModuleSingletonSmul r m) BHist.Empty) ∧
              ModuleSingletonClassifier o o' := by
  -- BEDC touchpoint anchor: BHist hsame ModuleSingletonCarrier ModuleSingletonClassifier
  intro _carrierR _carrierM fiberO fiberO'
  have endpointsO :
      hsame (ModuleSingletonSmul r m) BHist.Empty ∧ hsame o BHist.Empty :=
    Iff.mp ModuleSingletonClassifier_empty_endpoints_iff fiberO
  have endpointsO' :
      hsame (ModuleSingletonSmul r m) BHist.Empty ∧ hsame o' BHist.Empty :=
    Iff.mp ModuleSingletonClassifier_empty_endpoints_iff fiberO'
  have outputClassified : ModuleSingletonClassifier o o' :=
    Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
      (And.intro endpointsO.right endpointsO'.right)
  exact
    ⟨⟨endpointsO.right, endpointsO'.right, endpointsO.left⟩, outputClassified⟩

end BEDC.Derived.ModuleUp
