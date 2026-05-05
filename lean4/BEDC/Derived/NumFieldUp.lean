import BEDC.Derived.FieldExtUp.RatReflexive
import BEDC.Derived.FieldExtUp.RatReflexiveEmbedding
import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable
import BEDC.Derived.FieldExtUp.RatReflexiveSourcePattern
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

def NumFieldRatReflexiveCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h)

theorem NumFieldReflexiveRational_fieldext_scope {h r m action : BHist} :
    NumFieldRatReflexiveCarrier h -> RatHistoryCarrier r -> RatHistoryCarrier m ->
      Cont (FieldExtSingletonEmbedding r) m action ->
        RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
          RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
            RatHistoryCarrier action ∧ RatHistoryClassifier (FieldExtSingletonEmbedding r) r := by
  intro carrierH carrierR carrierM actionCont
  have productCont : Cont r m (append r m) :=
    cont_intro rfl
  have operationRows :
      RatHistoryClassifier (append r m) action ∧ RatHistoryCarrier (append r m) ∧
        RatHistoryCarrier action ∧ RatHistoryClassifier (FieldExtSingletonEmbedding r) r :=
    FieldExtRatReflexive_operation_table_source_coverage
      (And.intro carrierR (And.intro carrierR (hsame_refl r)))
      (And.intro carrierM (And.intro carrierM (hsame_refl m)))
      productCont actionCont
  exact And.intro carrierH.right.left
    (And.intro carrierH.right.right.right
      (And.intro operationRows.right.right.left operationRows.right.right.right))

theorem NumFieldRatReflexive_finite_basis_witness {h : BHist} :
    NumFieldRatReflexiveCarrier h ->
      RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
        Cont h (BHist.e1 BHist.Empty) (append h (BHist.e1 BHist.Empty)) ∧
          RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
            (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) := by
  intro carrier
  have basisCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have basisContinuation : Cont h (BHist.e1 BHist.Empty) (append h (BHist.e1 BHist.Empty)) :=
    cont_intro rfl
  have sourceClassified : RatHistoryClassifier h (FieldExtSingletonEmbedding h) :=
    RatHistoryLedgerPolicy_raw_visible_classifier carrier.right.right.right
  have appendedClassified :
      RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    RatHistoryClassifier_append_unary_denominator_closed sourceClassified
      (unary_e1_closed unary_empty) (hsame_refl (BHist.e1 BHist.Empty))
  exact And.intro basisCarrier (And.intro basisContinuation appendedClassified)

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

theorem NumFieldRatReflexive_namecert_obligations {h k r m coord action product : BHist} :
    RatHistoryClassifier h k -> RatHistoryCarrier r -> RatHistoryCarrier m ->
      Cont m BHist.Empty coord -> Cont (FieldExtSingletonEmbedding r) m action ->
        Cont r m product ->
          SemanticNameCert RatHistoryCarrier
              (fun z : BHist => RatHistoryCarrier (FieldExtSingletonEmbedding z))
              (fun z : BHist => RatHistoryLedgerPolicy z (FieldExtSingletonEmbedding z))
              RatHistoryClassifier ∧
            RatHistoryClassifier coord m ∧
              RatHistoryClassifier product action ∧
                RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
                  RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) := by
  intro classifiedHK carrierR carrierM coordReadback actionCont productCont
  have fieldExtRows := FieldExtRatReflexive_public_name_certificate
  have coordRows :=
    NumFieldReflexiveRational_finite_extension_witness carrierM coordReadback
  have ledgerRows :=
    FieldExtRatReflexive_ledger_provenance classifiedHK carrierR carrierM productCont actionCont
  exact And.intro fieldExtRows.left
    (And.intro coordRows.left
      (And.intro ledgerRows.right.right.left
        (And.intro ledgerRows.left ledgerRows.right.left)))

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
