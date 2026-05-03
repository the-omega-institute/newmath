import BEDC.Derived.FieldUp.RatDenomUnitEndpointAbsurd

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem RatDenomUnitCarrier_visible_cases_iff {h : BHist} :
    RatDenomUnitCarrier h <->
      hsame h BHist.Empty \/
        Exists (fun tail : BHist => h = BHist.e1 tail /\ UnaryHistory tail) := by
  constructor
  · exact RatDenomUnitCarrier_visible_cases
  · intro visible
    cases visible with
    | inl emptyCase =>
        cases emptyCase
        exact Or.inl (hsame_refl BHist.Empty)
    | inr headedCase =>
        cases headedCase with
        | intro tail data =>
            cases data with
            | intro hEq tailCarrier =>
                cases hEq
                exact RatDenomUnitCarrier_e1_tail_unary_iff.mpr tailCarrier

theorem RatDenomUnitClassifier_visible_cases_iff {h k : BHist} :
    RatDenomUnitClassifier h k <->
      (hsame h BHist.Empty /\ hsame k BHist.Empty) \/
        (Exists (fun htail : BHist =>
          Exists (fun ktail : BHist =>
            h = BHist.e1 htail /\ k = BHist.e1 ktail /\ UnaryHistory htail /\
              UnaryHistory ktail /\ hsame htail ktail))) := by
  constructor
  · intro classified
    have hCases := RatDenomUnitCarrier_visible_cases classified.left
    have kCases := RatDenomUnitCarrier_visible_cases classified.right.left
    cases hCases with
    | inl hEmpty =>
        cases kCases with
        | inl kEmpty =>
            left
            exact ⟨hEmpty, kEmpty⟩
        | inr kHeaded =>
            cases kHeaded with
            | intro ktail kData =>
                cases kData with
                | intro kEq _ktailCarrier =>
                    cases hEmpty
                    cases kEq
                    exact False.elim (not_hsame_emp_e1 classified.right.right)
    | inr hHeaded =>
        cases hHeaded with
        | intro htail hData =>
            cases hData with
            | intro hEq htailCarrier =>
                cases kCases with
                | inl kEmpty =>
                    cases hEq
                    cases kEmpty
                    exact False.elim (not_hsame_e1_empty classified.right.right)
                | inr kHeaded =>
                    cases kHeaded with
                    | intro ktail kData =>
                        cases kData with
                        | intro kEq ktailCarrier =>
                            right
                            cases hEq
                            cases kEq
                            exact Exists.intro htail
                              (Exists.intro ktail
                                ⟨rfl, rfl, htailCarrier, ktailCarrier,
                                  hsame_e1_iff.mp classified.right.right⟩)
  · intro visible
    cases visible with
    | inl emptyCases =>
        cases emptyCases with
        | intro hEmpty kEmpty =>
            cases hEmpty
            cases kEmpty
            exact ⟨Or.inl (hsame_refl BHist.Empty), Or.inl (hsame_refl BHist.Empty),
              hsame_refl BHist.Empty⟩
    | inr headedCases =>
        cases headedCases with
        | intro htail ktailCases =>
            cases ktailCases with
            | intro ktail data =>
                cases data with
                | intro hEq rest =>
                    cases rest with
                    | intro kEq rest =>
                        cases rest with
                        | intro htailCarrier rest =>
                            cases rest with
                            | intro ktailCarrier sameTail =>
                                cases hEq
                                cases kEq
                                exact
                                  ⟨RatDenomUnitCarrier_e1_tail_unary_iff.mpr htailCarrier,
                                    RatDenomUnitCarrier_e1_tail_unary_iff.mpr ktailCarrier,
                                    hsame_e1_iff.mpr sameTail⟩

theorem RatDenomUnitCarrier_append_e1_result_cases {h k tail : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> hsame (append h k) (BHist.e1 tail) ->
      (hsame k BHist.Empty ∧ RatDenomUnitCarrier (BHist.e1 tail) ∧
          hsame h (BHist.e1 tail)) ∨
        ∃ k0 : BHist,
          k = BHist.e1 k0 ∧ UnaryHistory k0 ∧ RatDenomUnitCarrier tail ∧
            Cont h k0 tail := by
  intro carrierH carrierK productSame
  have productCont : Cont h k (BHist.e1 tail) := hsame_symm productSame
  have resultCases := cont_e1_result_inversion productCont
  cases resultCases with
  | inl emptyTail =>
      cases emptyTail with
      | intro kEmpty hSame =>
          cases kEmpty
          left
          exact
            And.intro (hsame_refl BHist.Empty)
              (And.intro
                (RatDenomUnitCarrier_continuation_closed carrierH
                  (Or.inl (hsame_refl BHist.Empty)) productCont)
                hSame)
  | inr headedTail =>
      cases headedTail with
      | intro k0 headedData =>
          cases headedData with
          | intro kEq tailCont =>
              right
              cases kEq
              have k0Unary : UnaryHistory k0 :=
                RatDenomUnitCarrier_e1_tail_unary_iff.mp carrierK
              have carrierK0 : RatDenomUnitCarrier k0 :=
                RatDenomUnitCarrier_visible_cases_iff.mpr (unary_history_cases k0Unary)
              have tailCarrier : RatDenomUnitCarrier tail :=
                RatDenomUnitCarrier_continuation_closed carrierH carrierK0 tailCont
              exact Exists.intro k0
                (And.intro rfl (And.intro k0Unary (And.intro tailCarrier tailCont)))

end BEDC.Derived.FieldUp
