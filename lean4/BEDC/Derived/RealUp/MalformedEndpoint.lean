import BEDC.Derived.RealUp.EndpointAbsurd
import BEDC.Derived.RealUp.MalformedSealedDenominator

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist

def MalformedRealEndpoint (h : BHist) : Prop :=
  hsame h BHist.Empty ∨
    (exists t : BHist, hsame h (BHist.e0 t)) ∨
      MalformedRealSealedDenom h

theorem RealConstantHistoryClassifier_no_transported_malformed_endpoint_displays
    {h k h' k' : BHist} :
    RealConstantHistoryClassifier h k -> hsame h h' -> hsame k k' ->
      (MalformedRealEndpoint h' -> False) ∧
        (MalformedRealEndpoint k' -> False) := by
  intro classified sameH sameK
  have transported : RealConstantHistoryClassifier h' k' :=
    RealConstantHistoryClassifier_endpoint_transport sameH sameK classified
  have invalid := RealConstantHistoryClassifier_invalid_endpoint_absurd
  have leftSealed : MalformedRealSealedDenom h' -> False := by
    intro sealed
    cases sealed with
    | inl sameEmpty =>
        exact (RealConstantHistoryClassifier_transported_inner_empty_endpoint_absurd
          transported).left sameEmpty
    | inr rest =>
        cases rest with
        | inl zeroDisplay =>
            cases zeroDisplay with
            | intro tail sameZero =>
                exact (RealConstantHistoryClassifier_transported_inner_e0_endpoint_absurd
                  transported).left sameZero
        | inr appendedDisplay =>
            cases appendedDisplay with
            | intro p rest =>
                cases rest with
                | intro z sameAppend =>
                    exact (RealConstantHistoryClassifier_transported_malformed_inner_denominator_absurd
                      (pH := p) (zH := z) (pK := p) (zK := z) transported).right.left
                      sameAppend
  have rightSealed : MalformedRealSealedDenom k' -> False := by
    intro sealed
    cases sealed with
    | inl sameEmpty =>
        exact (RealConstantHistoryClassifier_transported_inner_empty_endpoint_absurd
          transported).right sameEmpty
    | inr rest =>
        cases rest with
        | inl zeroDisplay =>
            cases zeroDisplay with
            | intro tail sameZero =>
                exact (RealConstantHistoryClassifier_transported_inner_e0_endpoint_absurd
                  transported).right sameZero
        | inr appendedDisplay =>
            cases appendedDisplay with
            | intro p rest =>
                cases rest with
                | intro z sameAppend =>
                    exact (RealConstantHistoryClassifier_transported_malformed_inner_denominator_absurd
                      (pH := p) (zH := z) (pK := p) (zK := z) transported).right.right
                      sameAppend
  constructor
  · intro malformed
    cases malformed with
    | inl sameEmpty =>
        exact invalid.right.right.left
          (RealConstantHistoryClassifier_endpoint_transport sameEmpty (hsame_refl k')
            transported)
    | inr rest =>
        cases rest with
        | inl zeroDisplay =>
            cases zeroDisplay with
            | intro tail sameZero =>
                exact invalid.left
                  (RealConstantHistoryClassifier_endpoint_transport sameZero (hsame_refl k')
                    transported)
        | inr sealed =>
            exact leftSealed sealed
  · intro malformed
    cases malformed with
    | inl sameEmpty =>
        exact invalid.right.right.right
          (RealConstantHistoryClassifier_endpoint_transport (hsame_refl h') sameEmpty
            transported)
    | inr rest =>
        cases rest with
        | inl zeroDisplay =>
            cases zeroDisplay with
            | intro tail sameZero =>
                exact invalid.right.left
                  (RealConstantHistoryClassifier_endpoint_transport (hsame_refl h') sameZero
                    transported)
        | inr sealed =>
            exact rightSealed sealed

end BEDC.Derived.RealUp
