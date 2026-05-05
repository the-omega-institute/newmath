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

theorem ModuleSingleton_scalar_negation_action_additive_inverse {r m : BHist} :
    ModuleSingletonCarrier r -> ModuleSingletonCarrier m ->
      hsame (append (ModuleSingletonSmul (ModuleSingletonNeg r) m)
          (ModuleSingletonSmul r m)) BHist.Empty ∧
        hsame (append (ModuleSingletonSmul r m)
          (ModuleSingletonSmul (ModuleSingletonNeg r) m)) BHist.Empty ∧
        ModuleSingletonClassifier
          (ModuleSingletonAdd (ModuleSingletonSmul (ModuleSingletonNeg r) m)
            (ModuleSingletonSmul r m)) ModuleSingletonZero ∧
          ModuleSingletonClassifier
            (ModuleSingletonAdd (ModuleSingletonSmul r m)
              (ModuleSingletonSmul (ModuleSingletonNeg r) m)) ModuleSingletonZero := by
  intro _carrierR _carrierM
  have negActionEmpty : hsame (ModuleSingletonSmul (ModuleSingletonNeg r) m) BHist.Empty :=
    hsame_refl BHist.Empty
  have actionEmpty : hsame (ModuleSingletonSmul r m) BHist.Empty :=
    hsame_refl BHist.Empty
  have leftAppendEmpty :
      hsame (append (ModuleSingletonSmul (ModuleSingletonNeg r) m)
        (ModuleSingletonSmul r m)) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro negActionEmpty actionEmpty)
  have rightAppendEmpty :
      hsame (append (ModuleSingletonSmul r m)
        (ModuleSingletonSmul (ModuleSingletonNeg r) m)) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro actionEmpty negActionEmpty)
  have zeroEmpty : hsame ModuleSingletonZero BHist.Empty :=
    hsame_refl BHist.Empty
  have leftAddEmpty :
      hsame (ModuleSingletonAdd (ModuleSingletonSmul (ModuleSingletonNeg r) m)
        (ModuleSingletonSmul r m)) BHist.Empty :=
    hsame_refl BHist.Empty
  have rightAddEmpty :
      hsame (ModuleSingletonAdd (ModuleSingletonSmul r m)
        (ModuleSingletonSmul (ModuleSingletonNeg r) m)) BHist.Empty :=
    hsame_refl BHist.Empty
  have leftClassified :
      ModuleSingletonClassifier
        (ModuleSingletonAdd (ModuleSingletonSmul (ModuleSingletonNeg r) m)
          (ModuleSingletonSmul r m)) ModuleSingletonZero :=
    And.intro leftAddEmpty
      (And.intro zeroEmpty (hsame_trans leftAddEmpty (hsame_symm zeroEmpty)))
  have rightClassified :
      ModuleSingletonClassifier
        (ModuleSingletonAdd (ModuleSingletonSmul r m)
          (ModuleSingletonSmul (ModuleSingletonNeg r) m)) ModuleSingletonZero :=
    And.intro rightAddEmpty
      (And.intro zeroEmpty (hsame_trans rightAddEmpty (hsame_symm zeroEmpty)))
  exact And.intro leftAppendEmpty
    (And.intro rightAppendEmpty (And.intro leftClassified rightClassified))

end BEDC.Derived.ModuleUp
