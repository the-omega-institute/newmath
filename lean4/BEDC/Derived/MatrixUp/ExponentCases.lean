import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MatrixSingletonPow_unary_exponent_cases {M exponent : BHist} :
    UnaryHistory exponent ->
      MatrixSingletonClassifier (MatrixSingletonPow M exponent) MatrixSingletonOne ∨
        ∃ tail : BHist, UnaryHistory tail ∧
          Cont (MatrixSingletonPow M tail) M (MatrixSingletonPow M exponent) := by
  intro exponentUnary
  cases exponent with
  | Empty =>
      exact Or.inl
        (And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))
  | e0 tail =>
      cases exponentUnary
  | e1 tail =>
      exact Or.inr
        (Exists.intro tail (And.intro (unary_e1_inversion exponentUnary) (cont_intro rfl)))

theorem MatrixSingletonPow_empty_exponent_classifier_iff {M h : BHist} :
    MatrixSingletonClassifier (MatrixSingletonPow M BHist.Empty) h ↔
      MatrixSingletonCarrier h := by
  constructor
  · intro classified
    exact classified.right.left
  · intro carrier
    exact And.intro (hsame_refl BHist.Empty) (And.intro carrier (hsame_symm carrier))

theorem MatrixSingletonPow_zero_head_exponent_classifier_iff {M e h : BHist} :
    MatrixSingletonClassifier (MatrixSingletonPow M (BHist.e0 e)) h ↔
      MatrixSingletonCarrier h := by
  constructor
  · intro classified
    exact classified.right.left
  · intro carrier
    exact And.intro (hsame_refl BHist.Empty) (And.intro carrier (hsame_symm carrier))

theorem MatrixSingletonPow_unary_exponent_carrier_or_base_carrier {M exponent : BHist} :
    UnaryHistory exponent -> MatrixSingletonCarrier (MatrixSingletonPow M exponent) ->
      hsame exponent BHist.Empty ∨ MatrixSingletonCarrier M := by
  intro exponentUnary powCarrier
  cases exponent with
  | Empty =>
      exact Or.inl (hsame_refl BHist.Empty)
  | e0 tail =>
      cases exponentUnary
  | e1 tail =>
      exact Or.inr (append_eq_empty_iff.mp powCarrier).right

end BEDC.Derived.MatrixUp
