import BEDC.Derived.FieldExtUp.RatReflexiveSourcePattern

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldReflexiveRational_finite_extension_witness {m coord : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty coord ->
      RatHistoryClassifier coord m ∧ RatHistoryCarrier (FieldExtSingletonEmbedding m) ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding m) m := by
  intro carrierM coordinateReadback
  have sameCoordM : hsame coord m :=
    cont_right_unit_result coordinateReadback
  have coordCarrier : RatHistoryCarrier coord :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameCoordM) carrierM
  have coordClassifier : RatHistoryClassifier coord m :=
    And.intro coordCarrier (And.intro carrierM sameCoordM)
  have embeddedCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding m) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left m)) carrierM
  have embeddedClassifier : RatHistoryClassifier (FieldExtSingletonEmbedding m) m := by
    unfold FieldExtSingletonEmbedding
    exact And.intro embeddedCarrier (And.intro carrierM (append_empty_left m))
  exact And.intro coordClassifier (And.intro embeddedCarrier embeddedClassifier)

theorem NumFieldRatReflexive_classifier_transport {h k r m out coord : BHist} :
    RatHistoryClassifier h k -> RatHistoryCarrier r -> RatHistoryCarrier m ->
      Cont (FieldExtSingletonEmbedding r) m out -> Cont m BHist.Empty coord ->
        RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
          RatHistoryCarrier (FieldExtSingletonEmbedding k) ∧
            RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
              Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
                Cont BHist.Empty k (FieldExtSingletonEmbedding k) ∧
                  RatHistoryCarrier out ∧ RatHistoryClassifier coord m := by
  intro classified carrierR carrierM actionCont coordinateReadback
  have fieldRows :
      RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
        RatHistoryCarrier (FieldExtSingletonEmbedding k) ∧
          RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
            Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
              Cont BHist.Empty k (FieldExtSingletonEmbedding k) ∧ RatHistoryCarrier out :=
    FieldExtRatReflexive_source_pattern_classifier_obligations
      classified carrierR carrierM actionCont
  have sameCoordM : hsame coord m :=
    cont_right_unit_result coordinateReadback
  have coordClassifier : RatHistoryClassifier coord m :=
    RatHistoryClassifier_hsame_transport (hsame_symm sameCoordM) (hsame_refl m)
      (And.intro carrierM (And.intro carrierM (hsame_refl m)))
  exact And.intro fieldRows.left
    (And.intro fieldRows.right.left
      (And.intro fieldRows.right.right.left
        (And.intro fieldRows.right.right.right.left
          (And.intro fieldRows.right.right.right.right.left
            (And.intro fieldRows.right.right.right.right.right coordClassifier)))))

theorem NumFieldRatReflexive_ledger_exactness
    {h k r r' m m' product action coord : BHist} :
    RatHistoryClassifier h k -> RatHistoryClassifier r r' -> RatHistoryClassifier m m' ->
      Cont r m product -> Cont (FieldExtSingletonEmbedding r') m' action ->
        Cont m' BHist.Empty coord ->
          RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
            RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
              PositiveUnaryDenominator (FieldExtSingletonEmbedding h) ∧
                PositiveUnaryDenominator (FieldExtSingletonEmbedding k) ∧
                  RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
                    RatHistoryCarrier action ∧ RatHistoryClassifier coord m' := by
  intro classifiedHK classifiedRR classifiedMM productCont actionCont coordinateReadback
  have fieldRows :
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
        RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
          PositiveUnaryDenominator (FieldExtSingletonEmbedding h) ∧
            PositiveUnaryDenominator (FieldExtSingletonEmbedding k) ∧
              RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
                RatHistoryCarrier action :=
    FieldExtRatReflexive_certificate_row_exhaustion
      classifiedHK classifiedRR classifiedMM productCont actionCont
  have sameCoordM : hsame coord m' :=
    cont_right_unit_result coordinateReadback
  have coordClassifier : RatHistoryClassifier coord m' :=
    RatHistoryClassifier_hsame_transport (hsame_symm sameCoordM) (hsame_refl m')
      (And.intro classifiedMM.right.left
        (And.intro classifiedMM.right.left (hsame_refl m')))
  exact And.intro fieldRows.left
    (And.intro fieldRows.right.left
      (And.intro fieldRows.right.right.left
        (And.intro fieldRows.right.right.right.left
          (And.intro fieldRows.right.right.right.right.left
            (And.intro fieldRows.right.right.right.right.right.left
              (And.intro fieldRows.right.right.right.right.right.right coordClassifier))))))

end BEDC.Derived.NumFieldUp
