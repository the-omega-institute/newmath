import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RealConstantHistoryClassifier_e1_e0_endpoint_absurd {tail d : BHist} :
    (RealConstantHistoryClassifier (BHist.e1 (BHist.e0 tail)) (BHist.e1 d) -> False) ∧
      (RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 (BHist.e0 tail)) ->
        False) := by
  constructor
  · intro classified
    have ratClassified : RatHistoryClassifier (BHist.e0 tail) d :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    exact (RatHistoryClassifier_e0_endpoint_absurd (tail := tail) (d := d)).left
      ratClassified
  · intro classified
    have ratClassified : RatHistoryClassifier d (BHist.e0 tail) :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    exact (RatHistoryClassifier_e0_endpoint_absurd (tail := tail) (d := d)).right
      ratClassified

theorem RealConstantHistoryClassifier_e1_append_e0_endpoint_absurd {head tail d : BHist} :
    (RealConstantHistoryClassifier (BHist.e1 (append head (BHist.e0 tail))) (BHist.e1 d) ->
        False) ∧
      (RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 (append head (BHist.e0 tail))) ->
        False) := by
  constructor
  · intro classified
    have ratClassified : RatHistoryClassifier (append head (BHist.e0 tail)) d :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    have positives :
        PositiveUnaryDenominator (append head (BHist.e0 tail)) ∧
          PositiveUnaryDenominator d :=
      RatHistoryClassifier_positive_denominators ratClassified
    exact PositiveUnaryDenominator_append_e0_tail_absurd positives.left
  · intro classified
    have ratClassified : RatHistoryClassifier d (append head (BHist.e0 tail)) :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    have positives :
        PositiveUnaryDenominator d ∧ PositiveUnaryDenominator (append head (BHist.e0 tail)) :=
      RatHistoryClassifier_positive_denominators ratClassified
    exact PositiveUnaryDenominator_append_e0_tail_absurd positives.right

theorem RealConstantHistoryClassifier_transported_inner_e0_endpoint_absurd {h k tail : BHist} :
    RealConstantHistoryClassifier h k ->
      (hsame h (BHist.e1 (BHist.e0 tail)) -> False) ∧
        (hsame k (BHist.e1 (BHist.e0 tail)) -> False) := by
  intro classified
  cases classified with
  | intro d rest =>
      cases rest with
      | intro e data =>
          cases data with
          | intro sameH rest =>
              cases rest with
              | intro sameK ratClassified =>
                  constructor
                  · intro sameInner
                    have transported :
                        RealConstantHistoryClassifier
                          (BHist.e1 (BHist.e0 tail)) (BHist.e1 e) :=
                      RealConstantHistoryClassifier_endpoint_transport sameInner sameK
                        ⟨d, e, sameH, sameK, ratClassified⟩
                    exact (RealConstantHistoryClassifier_e1_e0_endpoint_absurd
                      (tail := tail) (d := e)).left transported
                  · intro sameInner
                    have transported :
                        RealConstantHistoryClassifier
                          (BHist.e1 d) (BHist.e1 (BHist.e0 tail)) :=
                      RealConstantHistoryClassifier_endpoint_transport sameH sameInner
                        ⟨d, e, sameH, sameK, ratClassified⟩
                    exact (RealConstantHistoryClassifier_e1_e0_endpoint_absurd
                      (tail := tail) (d := d)).right transported

end BEDC.Derived.RealUp
