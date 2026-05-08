import BEDC.Derived.RealUp.StreamBridge

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RealConstantHistory_semanticNameCert :
    SemanticNameCert RealConstantHistoryCarrier RealConstantHistoryCarrier
      RealConstantHistoryCarrier RealConstantHistoryClassifier := by
  have positiveDenominator : PositiveUnaryDenominator (BHist.e1 BHist.Empty) :=
    Iff.mpr PositiveUnaryDenominator_e1_iff_unary unary_empty
  have rationalCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    Iff.mpr RatHistoryCarrier_iff_positive_denominator positiveDenominator
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 (BHist.e1 BHist.Empty)) :=
    Iff.mpr RealConstantHistoryCarrier_e1_iff_rat rationalCarrier
  have fields := RealConstantHistoryClassifier_equivalence_fields
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro (BHist.e1 (BHist.e1 BHist.Empty)) realCarrier
      equiv_refl := by
        intro h carrier
        exact fields.left carrier
      equiv_symm := by
        intro h k classified
        exact fields.right.left classified
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact fields.right.right classifiedHK classifiedKR
      carrier_respects_equiv := by
        intro h k classified _carrier
        exact (RealConstantHistoryClassifier_endpoint_carriers classified).right
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem RealConstant_rational_embedding_certificate :
    SemanticNameCert RealConstantHistoryCarrier RealConstantHistoryCarrier
        RealConstantHistoryCarrier RealConstantHistoryClassifier ∧
      (forall {d : BHist},
        (RatHistoryCarrier d ↔ RatStreamNameCarrier (RatConstStream d)) ∧
          (RatStreamNameCarrier (RatConstStream d) ↔
            RealConstantHistoryCarrier (BHist.e1 d))) ∧
      (forall {d e : BHist},
        (RatHistoryClassifier d e ↔
          RatStreamNameClassifier (RatConstStream d) (RatConstStream e)) ∧
          (RatStreamNameClassifier (RatConstStream d) (RatConstStream e) ↔
            RealUnaryStreamClassifier (RatConstStream d) (RatConstStream e)) ∧
            (RealUnaryStreamClassifier (RatConstStream d) (RatConstStream e) ↔
              RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e))) := by
  constructor
  · exact RealConstantHistory_semanticNameCert
  · constructor
    · intro d
      exact (RealConstantStreamCarrier_streamName_bridge (d := d)).right
    · intro d e
      exact RealConstantStream_streamName_bridge (d := d) (e := e)

theorem RealUp_StdBridge :
    SemanticNameCert RealConstantHistoryCarrier RealConstantHistoryCarrier
        RealConstantHistoryCarrier RealConstantHistoryClassifier ∧
      (forall {d : BHist}, RatHistoryCarrier d ->
        RealConstantHistoryCarrier (BHist.e1 d)) ∧
      (forall {d e : BHist}, RatHistoryClassifier d e ->
        RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e)) ∧
      (forall {h k d e : BHist}, RealConstantHistoryClassifier h k ->
        hsame h (BHist.e1 d) -> hsame k (BHist.e1 e) -> RatHistoryClassifier d e) := by
  have cert := RealConstant_rational_embedding_certificate
  exact And.intro cert.left
    (And.intro
      (fun ratCarrier => Iff.mpr RealConstantHistoryCarrier_e1_iff_rat ratCarrier)
      (And.intro
        (fun ratClassifier => Iff.mpr RealConstantHistoryClassifier_e1_iff_rat ratClassifier)
        (fun realClassifier sameH sameK =>
          RealConstantHistoryClassifier_e1_tail_readback realClassifier sameH sameK)))

end BEDC.Derived.RealUp
