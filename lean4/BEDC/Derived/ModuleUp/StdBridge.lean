import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ModuleUp_StdBridge :
    SemanticNameCert ModuleSingletonCarrier ModuleSingletonCarrier ModuleSingletonCarrier
        ModuleSingletonClassifier ∧
      (forall {r m : BHist}, ModuleSingletonCarrier r -> ModuleSingletonCarrier m ->
        ModuleSingletonClassifier (ModuleSingletonSmul r m) BHist.Empty) ∧
      (forall {r m n : BHist}, ModuleSingletonCarrier r -> ModuleSingletonCarrier m ->
        ModuleSingletonClassifier (ModuleSingletonSmul r m) n ->
          ModuleSingletonCarrier n ∧ hsame n BHist.Empty) := by
  have laws := singleton_empty_history_module_laws
  constructor
  · exact laws.left
  · constructor
    · intro r m carrierR carrierM
      exact laws.right.left carrierR carrierM
    · intro r m n carrierR carrierM classified
      have graphExact := ModuleSingletonSmul_graph_empty_exact_iff (r := r) (m := m) (n := n)
      have carriers : ModuleSingletonCarrier r ∧ ModuleSingletonCarrier m ∧
          ModuleSingletonCarrier n :=
        Iff.mp graphExact.right (And.intro carrierR (And.intro carrierM classified))
      exact And.intro carriers.right.right carriers.right.right

end BEDC.Derived.ModuleUp
