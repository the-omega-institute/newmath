import BEDC.Derived.FieldUp.RatDenomUnitEndpointAbsurd

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatDenomUnitCarrier_visible_cases {h : BHist} :
    RatDenomUnitCarrier h ->
      hsame h BHist.Empty ∨ Exists (fun tail : BHist => h = BHist.e1 tail ∧ UnaryHistory tail) := by
  intro carrier
  cases h with
  | Empty =>
      left
      exact hsame_refl BHist.Empty
  | e0 tail =>
      exact False.elim (RatDenomUnitCarrier_e0_absurd carrier)
  | e1 tail =>
      right
      exact Exists.intro tail (And.intro rfl (RatDenomUnitCarrier_e1_tail_unary_iff.mp carrier))

theorem RatDenomUnitClassifier_visible_cases {h k : BHist} :
    RatDenomUnitClassifier h k ->
      (hsame h BHist.Empty ∧ hsame k BHist.Empty) ∨
        ∃ d e : BHist, h = BHist.e1 d ∧ k = BHist.e1 e ∧
          UnaryHistory d ∧ UnaryHistory e ∧ hsame d e := by
  intro classified
  have hCases := RatDenomUnitCarrier_visible_cases classified.left
  have kCases := RatDenomUnitCarrier_visible_cases classified.right.left
  cases hCases with
  | inl hEmpty =>
      cases kCases with
      | inl kEmpty =>
          left
          exact And.intro hEmpty kEmpty
      | inr kVisible =>
          cases kVisible with
          | intro e kData =>
              cases kData with
              | intro kEq _eCarrier =>
                  cases kEq
                  exact False.elim
                    (not_hsame_emp_e1
                      (hsame_trans (hsame_symm hEmpty) classified.right.right))
  | inr hVisible =>
      cases hVisible with
      | intro d hData =>
          cases hData with
          | intro hEq dCarrier =>
              cases hEq
              cases kCases with
              | inl kEmpty =>
                  exact False.elim
                    (not_hsame_e1_empty (hsame_trans classified.right.right kEmpty))
              | inr kVisible =>
                  cases kVisible with
                  | intro e kData =>
                      cases kData with
                      | intro kEq eCarrier =>
                          cases kEq
                          right
                          have sameDE : hsame d e := hsame_e1_iff.mp classified.right.right
                          exact Exists.intro d
                            (Exists.intro e
                              (And.intro rfl
                                (And.intro rfl
                                  (And.intro dCarrier (And.intro eCarrier sameDE)))))

end BEDC.Derived.FieldUp
