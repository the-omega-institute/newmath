import BEDC.Derived.FieldExtUp.RatReflexiveEmbedding
import BEDC.Derived.FieldExtUp.RatReflexiveSemanticCertificate

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp
open BEDC.Derived.FieldExtUp

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

end BEDC.Derived.NumFieldUp
