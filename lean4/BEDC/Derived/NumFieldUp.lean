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

theorem NumFieldRatReflexiveSingletonBasis_scalar_transport {r m coord product action : BHist} :
    RatHistoryCarrier r -> RatHistoryCarrier m -> Cont m BHist.Empty coord ->
      Cont r m product -> Cont (FieldExtSingletonEmbedding r) coord action ->
        RatHistoryClassifier action product ∧ PositiveUnaryDenominator action ∧
          PositiveUnaryDenominator product := by
  intro carrierR carrierM coordinateReadback productCont actionCont
  have sameCoordM : hsame coord m :=
    cont_right_unit_result coordinateReadback
  have actionOverM : Cont (FieldExtSingletonEmbedding r) m action :=
    cont_hsame_transport (hsame_refl (FieldExtSingletonEmbedding r)) sameCoordM
      (hsame_refl action) actionCont
  exact FieldExtRatReflexive_scalar_action_readback carrierR carrierM actionOverM productCont

theorem NumFieldRatReflexiveSingletonBasis_ledger_exactness
    {h k r r' m m' coord product action : BHist} :
    RatHistoryClassifier h k -> RatHistoryClassifier r r' -> RatHistoryClassifier m m' ->
      Cont m' BHist.Empty coord -> Cont r m product ->
        Cont (FieldExtSingletonEmbedding r') coord action ->
          RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
            RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
              PositiveUnaryDenominator (FieldExtSingletonEmbedding h) ∧
                PositiveUnaryDenominator (FieldExtSingletonEmbedding k) ∧
                  RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
                    RatHistoryCarrier action ∧ RatHistoryClassifier coord m' := by
  intro classifiedHK classifiedRR classifiedMM coordinateReadback productCont actionCont
  have sameCoordM : hsame coord m' :=
    cont_right_unit_result coordinateReadback
  have actionOverM : Cont (FieldExtSingletonEmbedding r') m' action :=
    cont_hsame_transport (hsame_refl (FieldExtSingletonEmbedding r')) sameCoordM
      (hsame_refl action) actionCont
  have fieldRows :=
    FieldExtRatReflexive_certificate_row_exhaustion classifiedHK classifiedRR classifiedMM
      productCont actionOverM
  have coordCarrier : RatHistoryCarrier coord :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameCoordM) classifiedMM.right.left
  have coordClassifier : RatHistoryClassifier coord m' :=
    And.intro coordCarrier (And.intro classifiedMM.right.left sameCoordM)
  exact And.intro fieldRows.left
    (And.intro fieldRows.right.left
      (And.intro fieldRows.right.right.left
        (And.intro fieldRows.right.right.right.left
          (And.intro fieldRows.right.right.right.right.left
            (And.intro fieldRows.right.right.right.right.right.left
              (And.intro fieldRows.right.right.right.right.right.right coordClassifier))))))

end BEDC.Derived.NumFieldUp
