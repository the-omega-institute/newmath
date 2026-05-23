import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Hist

def CauchyConvergenceCriterionObligationSurface
    (x : CauchyConvergenceCriterionUp) : Prop :=
  ∃ S M D R E H C P N : BHist,
    x = CauchyConvergenceCriterionUp.mk S M D R E H C P N ∧
      cauchyConvergenceCriterionFields x = [S, M, D, R, E, H, C, P, N] ∧
        hsame
          (cauchyConvergenceCriterionDecodeBHist
            (cauchyConvergenceCriterionEncodeBHist S))
          S ∧
          hsame
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist M))
            M ∧
            hsame
              (cauchyConvergenceCriterionDecodeBHist
                (cauchyConvergenceCriterionEncodeBHist D))
              D ∧
              hsame
                (cauchyConvergenceCriterionDecodeBHist
                  (cauchyConvergenceCriterionEncodeBHist R))
                R ∧
                hsame
                  (cauchyConvergenceCriterionDecodeBHist
                    (cauchyConvergenceCriterionEncodeBHist E))
                  E

theorem CauchyConvergenceCriterionNameCertObligations :
    forall x : CauchyConvergenceCriterionUp,
      CauchyConvergenceCriterionObligationSurface x := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  intro x
  cases x with
  | mk S M D R E H C P N =>
      refine ⟨S, M, D, R, E, H, C, P, N, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · change
          cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist S) =
            S
        induction S with
        | Empty => rfl
        | e0 S ih => exact congrArg BHist.e0 ih
        | e1 S ih => exact congrArg BHist.e1 ih
      · change
          cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist M) =
            M
        induction M with
        | Empty => rfl
        | e0 M ih => exact congrArg BHist.e0 ih
        | e1 M ih => exact congrArg BHist.e1 ih
      · change
          cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist D) =
            D
        induction D with
        | Empty => rfl
        | e0 D ih => exact congrArg BHist.e0 ih
        | e1 D ih => exact congrArg BHist.e1 ih
      · change
          cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist R) =
            R
        induction R with
        | Empty => rfl
        | e0 R ih => exact congrArg BHist.e0 ih
        | e1 R ih => exact congrArg BHist.e1 ih
      · change
          cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist E) =
            E
        induction E with
        | Empty => rfl
        | e0 E ih => exact congrArg BHist.e0 ih
        | e1 E ih => exact congrArg BHist.e1 ih

end BEDC.Derived.CauchyConvergenceCriterionUp
