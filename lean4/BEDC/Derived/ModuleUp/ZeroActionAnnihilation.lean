import BEDC.Derived.ModuleUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ModuleSingleton_zero_action_annihilation {r m : BHist} :
    ModuleSingletonCarrier r -> ModuleSingletonCarrier m ->
      hsame ModuleSingletonZero BHist.Empty ∧
        ModuleSingletonClassifier (ModuleSingletonSmul ModuleSingletonZero m) ModuleSingletonZero ∧
          ModuleSingletonClassifier (ModuleSingletonSmul r ModuleSingletonZero) ModuleSingletonZero ∧
            hsame (append (ModuleSingletonSmul ModuleSingletonZero m)
              (ModuleSingletonSmul r ModuleSingletonZero)) BHist.Empty := by
  intro _carrierR _carrierM
  have zeroEmpty : hsame ModuleSingletonZero BHist.Empty := hsame_refl BHist.Empty
  have leftActionEmpty : hsame (ModuleSingletonSmul ModuleSingletonZero m) BHist.Empty :=
    hsame_refl BHist.Empty
  have rightActionEmpty : hsame (ModuleSingletonSmul r ModuleSingletonZero) BHist.Empty :=
    hsame_refl BHist.Empty
  have leftClassified :
      ModuleSingletonClassifier (ModuleSingletonSmul ModuleSingletonZero m) ModuleSingletonZero :=
    And.intro leftActionEmpty
      (And.intro zeroEmpty (hsame_trans leftActionEmpty (hsame_symm zeroEmpty)))
  have rightClassified :
      ModuleSingletonClassifier (ModuleSingletonSmul r ModuleSingletonZero) ModuleSingletonZero :=
    And.intro rightActionEmpty
      (And.intro zeroEmpty (hsame_trans rightActionEmpty (hsame_symm zeroEmpty)))
  have actionsAppendEmpty :
      hsame (append (ModuleSingletonSmul ModuleSingletonZero m)
        (ModuleSingletonSmul r ModuleSingletonZero)) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro leftActionEmpty rightActionEmpty)
  exact And.intro zeroEmpty
    (And.intro leftClassified (And.intro rightClassified actionsAppendEmpty))

end BEDC.Derived.ModuleUp
