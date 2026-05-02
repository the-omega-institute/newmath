import BEDC.Derived.FieldUp
import BEDC.Derived.ModuleUp

namespace BEDC.Derived.VecSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.ModuleUp

theorem singleton_empty_history_vecspace_laws :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
      FieldSingletonClassifier ∧
      SemanticNameCert ModuleSingletonCarrier ModuleSingletonCarrier ModuleSingletonCarrier
      ModuleSingletonClassifier ∧
      (forall {a : BHist}, FieldSingletonCarrier a -> FieldSingletonNonZero a -> False) ∧
      (forall {r m : BHist}, FieldSingletonCarrier r -> ModuleSingletonCarrier m ->
        ModuleSingletonClassifier (ModuleSingletonSmul r m) BHist.Empty) ∧
      (forall {r r' m m' : BHist}, FieldSingletonClassifier r r' ->
        ModuleSingletonClassifier m m' ->
          ModuleSingletonClassifier (ModuleSingletonSmul r m) (ModuleSingletonSmul r' m')) ∧
      (forall {m : BHist}, ModuleSingletonCarrier m ->
        ModuleSingletonClassifier (ModuleSingletonSmul FieldSingletonOne m) m) := by
  have fieldLaws := BEDC.Derived.FieldUp.singleton_empty_history_field_schema_laws
  have moduleLaws := BEDC.Derived.ModuleUp.singleton_empty_history_module_laws
  have emptyModuleCarrier : ModuleSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyModuleClassified : ModuleSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyModuleCarrier
      (And.intro emptyModuleCarrier (hsame_refl BHist.Empty))
  constructor
  · exact fieldLaws.left
  · constructor
    · exact moduleLaws.left
    · constructor
      · exact fieldLaws.right.left
      · constructor
        · intro r m _carrierR _carrierM
          exact emptyModuleClassified
        · constructor
          · intro r r' m m' _sameR _sameM
            exact emptyModuleClassified
          · intro m carrierM
            exact And.intro emptyModuleCarrier
              (And.intro carrierM (hsame_symm carrierM))

end BEDC.Derived.VecSpaceUp
