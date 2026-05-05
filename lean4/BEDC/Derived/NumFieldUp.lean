import BEDC.Derived.FieldExtUp.RatReflexive
import BEDC.Derived.FieldExtUp.RatReflexiveEmbedding
import BEDC.Derived.FieldExtUp.RatReflexiveSemanticCertificate
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

def NumFieldReflexiveRationalCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ FieldExtRatReflexiveCarrier h ∧ Cont h BHist.Empty h

theorem NumFieldReflexiveRational_semantic_name_certificate :
    SemanticNameCert NumFieldReflexiveRationalCarrier NumFieldReflexiveRationalCarrier
      NumFieldReflexiveRationalCarrier RatHistoryClassifier := by
  have ratCert :
      SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier
        RatHistoryClassifier :=
    rat_history_semantic_name_certificate
  exact {
    core := {
      carrier_inhabited := by
        cases ratCert.core.carrier_inhabited with
        | intro h carrier =>
            exact Exists.intro h
              (And.intro carrier
                (And.intro (FieldExtRatReflexiveCarrier_rat_history_closure carrier)
                  (cont_right_unit h)))
      equiv_refl := by
        intro h carrier
        exact ratCert.core.equiv_refl carrier.left
      equiv_symm := by
        intro h k classified
        exact RatHistoryClassifier_symm classified
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact RatHistoryClassifier_trans classifiedHK classifiedKR
      carrier_respects_equiv := by
        intro h k classified carrierH
        have carrierK : RatHistoryCarrier k :=
          ratCert.core.carrier_respects_equiv classified carrierH.left
        exact And.intro carrierK
          (And.intro (FieldExtRatReflexiveCarrier_rat_history_closure carrierK)
            (cont_right_unit k))
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }

theorem NumFieldReflexiveRational_fieldext_consumption {h k : BHist} :
    NumFieldReflexiveRationalCarrier h -> NumFieldReflexiveRationalCarrier k ->
      RatHistoryClassifier h k ->
        FieldExtRatReflexiveCarrier h ∧ FieldExtRatReflexiveCarrier k ∧
          RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
            Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
              Cont BHist.Empty k (FieldExtSingletonEmbedding k) ∧
                Cont h BHist.Empty h ∧ Cont k BHist.Empty k := by
  intro carrierH carrierK classified
  have lock := FieldExtRatReflexive_source_pattern_lock classified
  exact And.intro carrierH.right.left
    (And.intro carrierK.right.left
      (And.intro lock.right.right.left
        (And.intro lock.right.right.right.left
          (And.intro lock.right.right.right.right
            (And.intro carrierH.right.right carrierK.right.right)))))

def NumFieldRatReflexiveCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h)

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
