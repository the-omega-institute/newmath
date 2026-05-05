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
    RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
      Cont BHist.Empty h (FieldExtSingletonEmbedding h)

def NumFieldRatReflexiveSingletonBasisRow (h coord support : BHist) : Prop :=
  support = BHist.Empty ∧ NumFieldRatReflexiveCarrier h ∧
    Cont h BHist.Empty coord ∧ RatHistoryClassifier coord h ∧
      RatHistoryCarrier (FieldExtSingletonEmbedding h)

def NumFieldRatReflexiveClassifier (h k : BHist) : Prop :=
  NumFieldRatReflexiveCarrier h ∧ NumFieldRatReflexiveCarrier k ∧ RatHistoryClassifier h k

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
    (And.intro carrierH.right.right.left
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
    RatHistoryLedgerPolicy_raw_visible_classifier carrier.right.right.left
  have appendedClassified :
      RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    RatHistoryClassifier_append_unary_denominator_closed sourceClassified
      (unary_e1_closed unary_empty) (hsame_refl (BHist.e1 BHist.Empty))
  exact And.intro basisCarrier (And.intro basisContinuation appendedClassified)

theorem NumFieldRatReflexive_basis_support_boundary :
    BEDC.Derived.VecSpaceUp.VecSpaceSingletonCarrier BHist.Empty ∧
      BEDC.Derived.FieldUp.FieldSingletonCarrier BHist.Empty ∧
        (RatHistoryCarrier BHist.Empty -> False) := by
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro (hsame_refl BHist.Empty)
      (by
        intro ratEmpty
        exact RatHistoryCarrier_not_empty ratEmpty (hsame_refl BHist.Empty)))

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

theorem NumFieldReflexiveRational_embedding_coordinate_classifier {m coord : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty coord ->
      RatHistoryClassifier (FieldExtSingletonEmbedding m) coord ∧ RatHistoryClassifier coord m ∧
        RatHistoryCarrier (FieldExtSingletonEmbedding m) ∧ RatHistoryCarrier coord := by
  intro carrierM coordinateReadback
  have witness :=
    NumFieldReflexiveRational_finite_extension_witness carrierM coordinateReadback
  have embeddedCoord : RatHistoryClassifier (FieldExtSingletonEmbedding m) coord :=
    RatHistoryClassifier_trans witness.right.right (RatHistoryClassifier_symm witness.left)
  exact And.intro embeddedCoord
    (And.intro witness.left (And.intro witness.right.left witness.left.left))

theorem NumFieldReflexiveRational_coordinate_readback_pair_determinacy {m c0 c1 : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty c0 -> Cont m BHist.Empty c1 ->
      RatHistoryClassifier c0 c1 ∧ RatHistoryClassifier c0 m ∧ RatHistoryClassifier c1 m := by
  intro carrierM readback0 readback1
  have sameC0M : hsame c0 m :=
    cont_right_unit_result readback0
  have sameC1M : hsame c1 m :=
    cont_right_unit_result readback1
  have carrierC0 : RatHistoryCarrier c0 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameC0M) carrierM
  have carrierC1 : RatHistoryCarrier c1 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameC1M) carrierM
  have classifiedC0M : RatHistoryClassifier c0 m :=
    And.intro carrierC0 (And.intro carrierM sameC0M)
  have classifiedC1M : RatHistoryClassifier c1 m :=
    And.intro carrierC1 (And.intro carrierM sameC1M)
  have classifiedMC1 : RatHistoryClassifier m c1 :=
    RatHistoryClassifier_symm classifiedC1M
  have classifiedC0C1 : RatHistoryClassifier c0 c1 :=
    RatHistoryClassifier_trans classifiedC0M classifiedMC1
  exact And.intro classifiedC0C1 (And.intro classifiedC0M classifiedC1M)

theorem NumFieldReflexiveRational_coordinate_readback_uniqueness {m c0 c1 : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty c0 -> Cont m BHist.Empty c1 ->
      RatHistoryClassifier c0 c1 ∧ RatHistoryClassifier c0 m ∧
        RatHistoryClassifier c1 m := by
  intro carrierM leftReadback rightReadback
  have sameC0M : hsame c0 m := cont_right_unit_result leftReadback
  have sameC1M : hsame c1 m := cont_right_unit_result rightReadback
  have c0Carrier : RatHistoryCarrier c0 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameC0M) carrierM
  have c1Carrier : RatHistoryCarrier c1 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameC1M) carrierM
  have c0M : RatHistoryClassifier c0 m :=
    And.intro c0Carrier (And.intro carrierM sameC0M)
  have c1M : RatHistoryClassifier c1 m :=
    And.intro c1Carrier (And.intro carrierM sameC1M)
  have c0c1 : RatHistoryClassifier c0 c1 :=
    RatHistoryClassifier_trans c0M (RatHistoryClassifier_symm c1M)
  exact And.intro c0c1 (And.intro c0M c1M)

theorem NumFieldReflexiveRational_singleton_basis_transport {h basis coord : BHist} :
    NumFieldRatReflexiveCarrier h -> RatHistoryCarrier basis ->
      hsame basis (BHist.e1 BHist.Empty) -> Cont h basis coord ->
        RatHistoryClassifier coord (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) := by
  intro carrier basisCarrier sameBasis coordinateContinuation
  have sourceClassified : RatHistoryClassifier h (FieldExtSingletonEmbedding h) :=
    RatHistoryLedgerPolicy_raw_visible_classifier carrier.right.right.left
  have basisUnary : UnaryHistory basis :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp basisCarrier)).left
  have appendedClassified :
      RatHistoryClassifier (append h basis)
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    RatHistoryClassifier_append_unary_denominator_closed sourceClassified basisUnary sameBasis
  exact RatHistoryClassifier_hsame_transport (hsame_symm coordinateContinuation)
    (hsame_refl (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)))
    appendedClassified

theorem NumFieldReflexiveRational_source_scope :
    SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier RatHistoryClassifier ∧
      (forall {h k : BHist}, RatHistoryClassifier h k ->
        RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
          RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
            RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k)) ∧
        (forall {r m out : BHist}, RatHistoryCarrier r -> RatHistoryCarrier m ->
          Cont r m out -> RatHistoryCarrier out) := by
  have vectorPackage := FieldExtRatReflexive_vector_space_package
  constructor
  · exact vectorPackage.left
  · constructor
    · intro h k classified
      have locked := FieldExtRatReflexiveEmbedding_ledger_source_lock classified
      exact And.intro locked.left
        (And.intro locked.right.left locked.right.right.left)
    · intro r m out carrierR carrierM continuation
      exact vectorPackage.right.right carrierR carrierM continuation

theorem NumFieldReflexiveRational_fieldext_source_pattern_consumption {h k r m out : BHist} :
    RatHistoryClassifier h k -> NumFieldRatReflexiveCarrier r -> RatHistoryCarrier m ->
      Cont (FieldExtSingletonEmbedding r) m out ->
        RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
          RatHistoryCarrier (FieldExtSingletonEmbedding k) ∧
            RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
              Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
                Cont BHist.Empty k (FieldExtSingletonEmbedding k) ∧ RatHistoryCarrier out := by
  intro classified carrierR carrierM continuation
  have locked := FieldExtRatReflexiveEmbedding_ledger_source_lock classified
  have actionClassified :
      RatHistoryClassifier out (append (FieldExtSingletonEmbedding r) m) :=
    FieldExtRatReflexiveTower_scalar_action carrierR.right.left carrierM continuation
  exact And.intro (RatHistoryLedgerPolicy_visible_carrier locked.left)
    (And.intro (RatHistoryLedgerPolicy_visible_carrier locked.right.left)
      (And.intro locked.right.right.left
        (And.intro locked.right.right.right.left
          (And.intro locked.right.right.right.right actionClassified.left))))

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

theorem NumFieldRatReflexive_fieldext_consumption {h r m product action : BHist} :
    NumFieldRatReflexiveCarrier h -> RatHistoryCarrier r -> RatHistoryCarrier m ->
      Cont r m product -> Cont (FieldExtSingletonEmbedding r) m action ->
        RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
          RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
            RatHistoryCarrier action := by
  intro carrierH carrierR carrierM productCont actionCont
  have operationRows :
      RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
        RatHistoryCarrier action ∧ RatHistoryClassifier (FieldExtSingletonEmbedding r) r :=
    FieldExtRatReflexive_operation_table_source_coverage
      (And.intro carrierR (And.intro carrierR (hsame_refl r)))
      (And.intro carrierM (And.intro carrierM (hsame_refl m)))
      productCont actionCont
  exact And.intro carrierH.right.right.left
    (And.intro operationRows.left
      (And.intro operationRows.right.left operationRows.right.right.left))

theorem NumFieldRatReflexive_carrier_classifier {h k : BHist} :
    RatHistoryClassifier h k ->
      NumFieldRatReflexiveCarrier h ∧ NumFieldRatReflexiveCarrier k ∧
        NumFieldRatReflexiveClassifier h k ∧
          Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
            Cont BHist.Empty k (FieldExtSingletonEmbedding k) ∧
              RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) := by
  intro classified
  have locked := FieldExtRatReflexiveEmbedding_ledger_source_lock classified
  have hCarrier : NumFieldRatReflexiveCarrier h :=
    And.intro classified.left
      (And.intro locked.right.right.left.left
        (And.intro locked.left locked.right.right.right.left))
  have kCarrier : NumFieldRatReflexiveCarrier k :=
    And.intro classified.right.left
      (And.intro locked.right.right.left.right.left
        (And.intro locked.right.left locked.right.right.right.right))
  have numClassifier : NumFieldRatReflexiveClassifier h k :=
    And.intro hCarrier (And.intro kCarrier classified)
  exact And.intro hCarrier
    (And.intro kCarrier
      (And.intro numClassifier
        (And.intro locked.right.right.right.left
          (And.intro locked.right.right.right.right locked.right.right.left))))

theorem NumFieldReflexiveRational_namecert_obligation_package :
    SemanticNameCert NumFieldRatReflexiveCarrier NumFieldRatReflexiveCarrier
      NumFieldRatReflexiveCarrier NumFieldRatReflexiveClassifier ∧
      (forall {h k : BHist}, RatHistoryClassifier h k ->
        NumFieldRatReflexiveClassifier h k) ∧
      (forall {h k : BHist}, NumFieldRatReflexiveClassifier h k ->
        RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k)) := by
  have ratCert :
      SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier
        RatHistoryClassifier :=
    rat_history_semantic_name_certificate
  have semantic :
      SemanticNameCert NumFieldRatReflexiveCarrier NumFieldRatReflexiveCarrier
        NumFieldRatReflexiveCarrier NumFieldRatReflexiveClassifier := {
    core := {
      carrier_inhabited := by
        cases ratCert.core.carrier_inhabited with
        | intro h carrier =>
            exact Exists.intro h
              (NumFieldRatReflexive_carrier_classifier
                (ratCert.core.equiv_refl carrier)).left
      equiv_refl := by
        intro h carrier
        exact And.intro carrier
          (And.intro carrier (ratCert.core.equiv_refl carrier.left))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (ratCert.core.equiv_symm classified.right.right))
      equiv_trans := by
        intro h k r hk kr
        exact And.intro hk.left
          (And.intro kr.right.left
            (ratCert.core.equiv_trans hk.right.right kr.right.right))
      carrier_respects_equiv := by
        intro h k classified carrierH
        exact (NumFieldRatReflexive_carrier_classifier classified.right.right).right.left
    }
    pattern_sound := by
      intro h carrier
      exact (NumFieldRatReflexive_carrier_classifier
        (ratCert.core.equiv_refl carrier.left)).left
    ledger_sound := by
      intro h carrier
      exact (NumFieldRatReflexive_carrier_classifier
        (ratCert.core.equiv_refl carrier.left)).left
  }
  exact And.intro semantic
    (And.intro
      (by
        intro h k classified
        exact (NumFieldRatReflexive_carrier_classifier classified).right.right.left)
      (by
        intro h k classified
        exact (NumFieldRatReflexive_carrier_classifier classified.right.right).right.right.right.right.right))

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

theorem NumFieldRatReflexive_scoped_namecert_certificate :
    SemanticNameCert NumFieldRatReflexiveCarrier NumFieldRatReflexiveCarrier
        NumFieldRatReflexiveCarrier NumFieldRatReflexiveClassifier ∧
      (forall {h k : BHist}, RatHistoryClassifier h k ->
        NumFieldRatReflexiveClassifier h k ∧
          RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k)) ∧
      (forall {h : BHist}, NumFieldRatReflexiveCarrier h ->
        RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
          Cont h (BHist.e1 BHist.Empty) (append h (BHist.e1 BHist.Empty))) ∧
      (forall {h k r r' m m' product action coord : BHist},
        RatHistoryClassifier h k -> RatHistoryClassifier r r' -> RatHistoryClassifier m m' ->
          Cont r m product -> Cont (FieldExtSingletonEmbedding r') m' action ->
            Cont m' BHist.Empty coord ->
              RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
                RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
                  RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
                    RatHistoryCarrier action ∧ RatHistoryClassifier coord m') := by
  have package := NumFieldReflexiveRational_namecert_obligation_package
  constructor
  · exact package.left
  · constructor
    · intro h k classified
      exact And.intro (package.right.left classified) (package.right.right (package.right.left classified))
    · constructor
      · intro h carrier
        have basisRows := NumFieldRatReflexive_finite_basis_witness carrier
        exact And.intro basisRows.left basisRows.right.left
      · intro h k r r' m m' product action coord classifiedHK classifiedRR classifiedMM
          productCont actionCont coordCont
        have exactRows :=
          NumFieldRatReflexive_ledger_exactness classifiedHK classifiedRR classifiedMM
            productCont actionCont coordCont
        exact And.intro exactRows.left
          (And.intro exactRows.right.left
            (And.intro exactRows.right.right.right.right.left
              (And.intro exactRows.right.right.right.right.right.left
                (And.intro exactRows.right.right.right.right.right.right.left
                  exactRows.right.right.right.right.right.right.right))))

theorem NumFieldReflexiveRational_exactness_package
    {h k r r' m m' product action coord : BHist} :
    NumFieldRatReflexiveCarrier h -> RatHistoryClassifier h k ->
      RatHistoryClassifier r r' -> RatHistoryClassifier m m' -> Cont r m product ->
        Cont (FieldExtSingletonEmbedding r') m' action -> Cont m' BHist.Empty coord ->
          SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier
              RatHistoryClassifier ∧
            NumFieldRatReflexiveCarrier k ∧
              RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
                RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
                  RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
                    RatHistoryCarrier action ∧ RatHistoryClassifier coord m' := by
  intro carrierH classifiedHK classifiedRR classifiedMM productCont actionCont coordinateReadback
  have exactRows :
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
        RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
          PositiveUnaryDenominator (FieldExtSingletonEmbedding h) ∧
            PositiveUnaryDenominator (FieldExtSingletonEmbedding k) ∧
              RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
                RatHistoryCarrier action ∧ RatHistoryClassifier coord m' :=
    NumFieldRatReflexive_ledger_exactness classifiedHK classifiedRR classifiedMM
      productCont actionCont coordinateReadback
  have kCarrier : RatHistoryCarrier k := classifiedHK.right.left
  have kFieldCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding k) :=
    RatHistoryLedgerPolicy_visible_carrier exactRows.right.left
  have kContinuation : Cont BHist.Empty k (FieldExtSingletonEmbedding k) :=
    (FieldExtRatReflexiveEmbedding_ledger_source_lock classifiedHK).right.right.right.right
  have kNumCarrier : NumFieldRatReflexiveCarrier k :=
    And.intro kCarrier
      (And.intro kFieldCarrier (And.intro exactRows.right.left kContinuation))
  exact And.intro rat_history_semantic_name_certificate
    (And.intro kNumCarrier
      (And.intro exactRows.left
        (And.intro exactRows.right.left
            (And.intro exactRows.right.right.right.right.left
              (And.intro exactRows.right.right.right.right.right.left
                (And.intro exactRows.right.right.right.right.right.right.left
                  exactRows.right.right.right.right.right.right.right))))))

theorem NumFieldRatReflexive_fieldext_scope {h k r m product action : BHist} :
    RatHistoryClassifier h k -> RatHistoryCarrier r -> RatHistoryCarrier m ->
      Cont r m product -> Cont (FieldExtSingletonEmbedding r) m action ->
        SemanticNameCert RatHistoryCarrier
            (fun z : BHist => RatHistoryCarrier (FieldExtSingletonEmbedding z))
            (fun z : BHist => RatHistoryLedgerPolicy z (FieldExtSingletonEmbedding z))
            RatHistoryClassifier ∧
          RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
            RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
              RatHistoryClassifier product action ∧
                RatHistoryCarrier product ∧
                  RatHistoryCarrier action ∧ RatHistoryClassifier (FieldExtSingletonEmbedding r) r := by
  intro classifiedHK carrierR carrierM productCont actionCont
  have certRows := FieldExtRatReflexive_public_name_certificate
  have ledgerRows :=
    FieldExtRatReflexive_ledger_coverage classifiedHK carrierR carrierM productCont actionCont
  exact And.intro certRows.left ledgerRows

theorem NumFieldReflexiveRational_coordinate_embedding_pair_readback {m c0 c1 emb0 emb1 : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty c0 -> Cont m BHist.Empty c1 ->
      Cont BHist.Empty c0 emb0 -> Cont BHist.Empty c1 emb1 ->
        RatHistoryClassifier c0 c1 ∧ RatHistoryClassifier emb0 emb1 ∧
          RatHistoryClassifier emb0 m ∧ RatHistoryClassifier emb1 m ∧
            RatHistoryCarrier emb0 ∧ RatHistoryCarrier emb1 := by
  intro carrierM c0Readback c1Readback emb0Readback emb1Readback
  have sameC0M : hsame c0 m :=
    cont_right_unit_result c0Readback
  have sameC1M : hsame c1 m :=
    cont_right_unit_result c1Readback
  have carrierC0 : RatHistoryCarrier c0 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameC0M) carrierM
  have carrierC1 : RatHistoryCarrier c1 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameC1M) carrierM
  have sameEmb0C0 : hsame emb0 c0 :=
    cont_left_unit_result emb0Readback
  have sameEmb1C1 : hsame emb1 c1 :=
    cont_left_unit_result emb1Readback
  have carrierEmb0 : RatHistoryCarrier emb0 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameEmb0C0) carrierC0
  have carrierEmb1 : RatHistoryCarrier emb1 :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameEmb1C1) carrierC1
  have sameC0C1 : hsame c0 c1 :=
    hsame_trans sameC0M (hsame_symm sameC1M)
  have sameEmb0Emb1 : hsame emb0 emb1 :=
    hsame_trans sameEmb0C0 (hsame_trans sameC0C1 (hsame_symm sameEmb1C1))
  have sameEmb0M : hsame emb0 m :=
    hsame_trans sameEmb0C0 sameC0M
  have sameEmb1M : hsame emb1 m :=
    hsame_trans sameEmb1C1 sameC1M
  exact And.intro (And.intro carrierC0 (And.intro carrierC1 sameC0C1))
    (And.intro (And.intro carrierEmb0 (And.intro carrierEmb1 sameEmb0Emb1))
      (And.intro (And.intro carrierEmb0 (And.intro carrierM sameEmb0M))
        (And.intro (And.intro carrierEmb1 (And.intro carrierM sameEmb1M))
          (And.intro carrierEmb0 carrierEmb1))))

end BEDC.Derived.NumFieldUp
