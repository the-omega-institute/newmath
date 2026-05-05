import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingleton_semantic_name_certificate :
    SemanticNameCert FieldSingletonCarrier
      (fun h : BHist => FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h)
      (fun h : BHist => FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h)
      FieldSingletonClassifier := by
  have fieldCert :
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier :=
    singleton_empty_history_field_schema_laws.left
  exact {
    core := fieldCert.core
    pattern_sound := by
      intro _h source
      exact And.intro source source
    ledger_sound := by
      intro _h source
      exact And.intro source source
  }

theorem FieldExtSingleton_vector_action_field_mul_context_readback {L R r m out : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> VecSpaceSingletonCarrier m ->
      FieldSingletonClassifier (append L (VecSpaceSingletonSmul r m)) (append R out) ->
        FieldSingletonClassifier (append L (FieldSingletonMul r m)) (append R out) ∧
          hsame out BHist.Empty := by
  intro _carrierL _carrierR _carrierM classified
  have rightEmpty : append R out = BHist.Empty := classified.right.left
  have outEmpty : hsame out BHist.Empty := (append_eq_empty_iff.mp rightEmpty).right
  exact And.intro classified outEmpty

end BEDC.Derived.FieldExtUp
