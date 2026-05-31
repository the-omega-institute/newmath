import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyConvergenceCriterionCarrier_scope_window [AskSetup] [PackageSetup]
    (S M D R E H C P N : BHist) :
    cauchyConvergenceCriterionFromEventFlow
          (cauchyConvergenceCriterionToEventFlow
            (CauchyConvergenceCriterionUp.mk S M D R E H C P N)) =
        some (CauchyConvergenceCriterionUp.mk S M D R E H C P N) ∧
      Cont S M (append S M) ∧
      Cont M D (append M D) ∧
      Cont D R (append D R) ∧
      Cont R E (append R E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist,
        cauchyConvergenceCriterionDecodeBHist (cauchyConvergenceCriterionEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [cauchyConvergenceCriterionToEventFlow, cauchyConvergenceCriterionFromEventFlow,
      hdecode S, hdecode M, hdecode D, hdecode R, hdecode E, hdecode H,
      hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · rfl

end BEDC.Derived.CauchyConvergenceCriterionUp
