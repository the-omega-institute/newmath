import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FieldUp
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_scalar_action_readback {r m out product : BHist} :
    RatHistoryCarrier r -> RatHistoryCarrier m -> Cont (FieldExtSingletonEmbedding r) m out ->
      Cont r m product ->
        RatHistoryClassifier out product ∧ PositiveUnaryDenominator out ∧
          PositiveUnaryDenominator product := by
  intro carrierR carrierM actionCont productCont
  have positiveM : PositiveUnaryDenominator m :=
    RatHistoryCarrier_iff_positive_denominator.mp carrierM
  have unaryM : UnaryHistory m :=
    (PositiveUnaryDenominator_unary_and_nonempty positiveM).left
  have embeddedCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding r) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryCarrier_hsame_transport (append_empty_left r).symm carrierR
  have embeddedClassifier : RatHistoryClassifier (FieldExtSingletonEmbedding r) r := by
    unfold FieldExtSingletonEmbedding
    exact ⟨embeddedCarrier, carrierR, append_empty_left r⟩
  have appendedClassifier :
      RatHistoryClassifier (append (FieldExtSingletonEmbedding r) m) (append r m) :=
    RatHistoryClassifier_append_unary_denominator_closed embeddedClassifier unaryM (hsame_refl m)
  have actionSame : hsame (append (FieldExtSingletonEmbedding r) m) out :=
    actionCont.symm
  have productSame : hsame (append r m) product :=
    productCont.symm
  have readbackClassifier : RatHistoryClassifier out product :=
    RatHistoryClassifier_hsame_transport actionSame productSame appendedClassifier
  have positives :
      PositiveUnaryDenominator out ∧ PositiveUnaryDenominator product :=
    RatHistoryClassifier_positive_denominators readbackClassifier
  exact And.intro readbackClassifier (And.intro positives.left positives.right)

theorem FieldExtRatReflexive_operation_table_source_coverage
    {r r' m m' product action : BHist} :
    RatHistoryClassifier r r' -> RatHistoryClassifier m m' -> Cont r m product ->
      Cont (FieldExtSingletonEmbedding r') m' action ->
        RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
          RatHistoryCarrier action ∧ RatHistoryClassifier (FieldExtSingletonEmbedding r') r' := by
  intro classifiedR classifiedM productCont actionCont
  have endpointRows :
      RatHistoryClassifier (FieldExtSingletonEmbedding r') r' ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding r') r' ∧
          RatHistoryClassifier (FieldExtSingletonEmbedding r') (FieldExtSingletonEmbedding r') :=
    FieldExtRatReflexive_exact_endpoint_classification
      (RatHistoryClassifier_trans (RatHistoryClassifier_symm classifiedR) classifiedR)
  have embeddedSource :
      RatHistoryClassifier r (FieldExtSingletonEmbedding r') :=
    RatHistoryClassifier_trans classifiedR (RatHistoryClassifier_symm endpointRows.left)
  have productActionClassifier : RatHistoryClassifier product action :=
    field_rat_denominator_continuation_binary_classifier_congruence embeddedSource classifiedM
      productCont actionCont
  exact And.intro productActionClassifier
    (And.intro productActionClassifier.left
      (And.intro productActionClassifier.right.left endpointRows.left))

end BEDC.Derived.FieldExtUp
