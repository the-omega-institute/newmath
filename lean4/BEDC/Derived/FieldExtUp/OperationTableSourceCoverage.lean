import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_operation_table_source_coverage
    {h k r m out product : BHist} :
    RatHistoryClassifier h k → RatHistoryCarrier r → RatHistoryCarrier m →
      Cont r m product → Cont (FieldExtSingletonEmbedding r) m out →
        RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
          RatHistoryClassifier out product ∧ RatHistoryCarrier product := by
  intro classified carrierR carrierM productCont actionCont
  have sourceLock := FieldExtRatReflexive_source_pattern_lock classified
  have readback :=
    FieldExtRatReflexive_scalar_action_readback carrierR carrierM actionCont productCont
  have productCarrier : RatHistoryCarrier product :=
    RatHistoryCarrier_continuation_closed carrierR carrierM productCont
  exact ⟨sourceLock.right.right.left, readback.left, productCarrier⟩

end BEDC.Derived.FieldExtUp
