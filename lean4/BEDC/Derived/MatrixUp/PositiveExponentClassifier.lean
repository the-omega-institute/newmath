import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MatrixSingletonPow_positive_exponent_classifier_iff {M exponent h : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      (MatrixSingletonClassifier (MatrixSingletonPow M exponent) h ↔
        MatrixSingletonCarrier M ∧ MatrixSingletonCarrier h) := by
  intro exponentUnary exponentNonempty
  have baseIff :=
    MatrixSingletonPow_carrier_nonempty_unary_input_iff
      (M := M) (exponent := exponent) exponentUnary exponentNonempty
  constructor
  · intro classified
    exact And.intro (Iff.mp baseIff classified.left) classified.right.left
  · intro carriers
    have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M exponent) :=
      MatrixSingletonPow_carrier_closed carriers.left exponentUnary
    exact And.intro powCarrier
      (And.intro carriers.right (hsame_trans powCarrier (hsame_symm carriers.right)))

end BEDC.Derived.MatrixUp
