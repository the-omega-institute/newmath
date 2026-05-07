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

theorem RealConstantHistoryClassifier_e1_empty_endpoint_absurd {d : BHist} :
    (RealConstantHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 d) -> False) ∧
      (RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 BHist.Empty) -> False) := by
  constructor
  · intro classified
    have ratClassified : RatHistoryClassifier BHist.Empty d :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    exact (RatHistoryClassifier_endpoints_not_empty ratClassified).left
      (hsame_refl BHist.Empty)
  · intro classified
    have ratClassified : RatHistoryClassifier d BHist.Empty :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    exact (RatHistoryClassifier_endpoints_not_empty ratClassified).right
      (hsame_refl BHist.Empty)

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

theorem RealConstantHistoryClassifier_transported_inner_empty_endpoint_absurd {h k : BHist} :
    RealConstantHistoryClassifier h k ->
      (hsame h (BHist.e1 BHist.Empty) -> False) ∧
        (hsame k (BHist.e1 BHist.Empty) -> False) := by
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
                        RealConstantHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 e) :=
                      RealConstantHistoryClassifier_endpoint_transport sameInner sameK
                        ⟨d, e, sameH, sameK, ratClassified⟩
                    exact (RealConstantHistoryClassifier_e1_empty_endpoint_absurd
                      (d := e)).left transported
                  · intro sameInner
                    have transported :
                        RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 BHist.Empty) :=
                      RealConstantHistoryClassifier_endpoint_transport sameH sameInner
                        ⟨d, e, sameH, sameK, ratClassified⟩
                    exact (RealConstantHistoryClassifier_e1_empty_endpoint_absurd
                      (d := d)).right transported

theorem RealConstantHistoryClassifier_transported_malformed_inner_denominator_absurd
    {h k pH zH pK zK : BHist} :
    RealConstantHistoryClassifier h k ->
      ((hsame h (BHist.e1 BHist.Empty) -> False) ∧
        (hsame k (BHist.e1 BHist.Empty) -> False)) ∧
        ((hsame h (BHist.e1 (append pH (BHist.e0 zH))) -> False) ∧
          (hsame k (BHist.e1 (append pK (BHist.e0 zK))) -> False)) := by
  intro classified
  have emptyExclusions :
      (hsame h (BHist.e1 BHist.Empty) -> False) ∧
        (hsame k (BHist.e1 BHist.Empty) -> False) :=
    RealConstantHistoryClassifier_transported_inner_empty_endpoint_absurd classified
  cases classified with
  | intro d rest =>
      cases rest with
      | intro e data =>
          cases data with
          | intro sameH rest =>
              cases rest with
              | intro sameK ratClassified =>
                  constructor
                  · exact emptyExclusions
                  · constructor
                    · intro sameMalformed
                      have transported :
                          RealConstantHistoryClassifier
                            (BHist.e1 (append pH (BHist.e0 zH))) (BHist.e1 e) :=
                        RealConstantHistoryClassifier_endpoint_transport sameMalformed sameK
                          ⟨d, e, sameH, sameK, ratClassified⟩
                      exact (RealConstantHistoryClassifier_e1_append_e0_endpoint_absurd
                        (head := pH) (tail := zH) (d := e)).left transported
                    · intro sameMalformed
                      have transported :
                          RealConstantHistoryClassifier (BHist.e1 d)
                            (BHist.e1 (append pK (BHist.e0 zK))) :=
                        RealConstantHistoryClassifier_endpoint_transport sameH sameMalformed
                          ⟨d, e, sameH, sameK, ratClassified⟩
                      exact (RealConstantHistoryClassifier_e1_append_e0_endpoint_absurd
                        (head := pK) (tail := zK) (d := d)).right transported

end BEDC.Derived.RealUp
