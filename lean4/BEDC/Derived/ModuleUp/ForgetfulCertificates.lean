import BEDC.Derived.AbGroupUp
import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ModuleSingleton_forgets_abgroup_certificate :
    SemanticNameCert BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonClassifier ∧
      (∀ {h : BHist}, ModuleSingletonCarrier h ->
        BEDC.Derived.GroupUp.GroupSingletonCarrier h) ∧
      (∀ {h k : BHist}, ModuleSingletonClassifier h k ->
        BEDC.Derived.GroupUp.GroupSingletonClassifier h k) ∧
      (∀ {h k : BHist}, ModuleSingletonCarrier h -> ModuleSingletonCarrier k ->
        BEDC.Derived.GroupUp.GroupSingletonClassifier (ModuleSingletonAdd h k) BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert ModuleSingletonCarrier
  have abgroupCert :
      SemanticNameCert BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonClassifier :=
    BEDC.Derived.AbGroupUp.singleton_empty_history_abgroup_laws.left
  have carrierForget :
      ∀ {h : BHist}, ModuleSingletonCarrier h ->
        BEDC.Derived.GroupUp.GroupSingletonCarrier h := by
    intro h carrierH
    exact carrierH
  have classifierForget :
      ∀ {h k : BHist}, ModuleSingletonClassifier h k ->
        BEDC.Derived.GroupUp.GroupSingletonClassifier h k := by
    intro h k classified
    exact classified
  have retainedAdd :
      ∀ {h k : BHist}, ModuleSingletonCarrier h -> ModuleSingletonCarrier k ->
        BEDC.Derived.GroupUp.GroupSingletonClassifier (ModuleSingletonAdd h k) BHist.Empty := by
    intro h k _carrierH _carrierK
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  exact ⟨abgroupCert, carrierForget, classifierForget, retainedAdd⟩

end BEDC.Derived.ModuleUp
