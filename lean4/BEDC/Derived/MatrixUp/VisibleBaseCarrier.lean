import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MatrixSingletonPow_visible_base_carrier_iff {m exponent : BHist} :
    (MatrixSingletonCarrier (MatrixSingletonPow (BHist.e0 m) exponent) ↔
      hsame exponent BHist.Empty ∨ ∃ tail : BHist, exponent = BHist.e0 tail) ∧
      (MatrixSingletonCarrier (MatrixSingletonPow (BHist.e1 m) exponent) ↔
        hsame exponent BHist.Empty ∨ ∃ tail : BHist, exponent = BHist.e0 tail) := by
  constructor
  · constructor
    · intro carrier
      cases exponent with
      | Empty =>
          exact Or.inl (hsame_refl BHist.Empty)
      | e0 tail =>
          exact Or.inr (Exists.intro tail rfl)
      | e1 tail =>
          have productParts := append_eq_empty_iff.mp carrier
          exact False.elim (not_hsame_e0_empty productParts.right)
    · intro exponentShape
      cases exponent with
      | Empty =>
          exact hsame_refl BHist.Empty
      | e0 tail =>
          exact hsame_refl BHist.Empty
      | e1 tail =>
          cases exponentShape with
          | inl exponentEmpty =>
              cases exponentEmpty
          | inr witness =>
              cases witness with
              | intro visibleTail visibleEq =>
                  cases visibleEq
  · constructor
    · intro carrier
      cases exponent with
      | Empty =>
          exact Or.inl (hsame_refl BHist.Empty)
      | e0 tail =>
          exact Or.inr (Exists.intro tail rfl)
      | e1 tail =>
          have productParts := append_eq_empty_iff.mp carrier
          exact False.elim (not_hsame_e1_empty productParts.right)
    · intro exponentShape
      cases exponent with
      | Empty =>
          exact hsame_refl BHist.Empty
      | e0 tail =>
          exact hsame_refl BHist.Empty
      | e1 tail =>
          cases exponentShape with
          | inl exponentEmpty =>
              cases exponentEmpty
          | inr witness =>
              cases witness with
              | intro visibleTail visibleEq =>
                  cases visibleEq

theorem MatrixSingletonPow_positive_exponent_visible_base_classifier_absurd {m exponent h : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      (MatrixSingletonClassifier (MatrixSingletonPow (BHist.e0 m) exponent) h -> False) ∧
      (MatrixSingletonClassifier (MatrixSingletonPow (BHist.e1 m) exponent) h -> False) := by
  intro exponentUnary exponentNonempty
  constructor
  · intro classified
    have exponentShape :=
      Iff.mp (MatrixSingletonPow_visible_base_carrier_iff (m := m) (exponent := exponent)).left
        classified.left
    cases exponent with
    | Empty =>
        exact exponentNonempty (hsame_refl BHist.Empty)
    | e0 tail =>
        cases exponentUnary
    | e1 tail =>
        cases exponentShape with
        | inl exponentEmpty =>
            cases exponentEmpty
        | inr witness =>
            cases witness with
            | intro visibleTail visibleEq =>
                cases visibleEq
  · intro classified
    have exponentShape :=
      Iff.mp (MatrixSingletonPow_visible_base_carrier_iff (m := m) (exponent := exponent)).right
        classified.left
    cases exponent with
    | Empty =>
        exact exponentNonempty (hsame_refl BHist.Empty)
    | e0 tail =>
        cases exponentUnary
    | e1 tail =>
        cases exponentShape with
        | inl exponentEmpty =>
            cases exponentEmpty
        | inr witness =>
            cases witness with
            | intro visibleTail visibleEq =>
                cases visibleEq

end BEDC.Derived.MatrixUp
