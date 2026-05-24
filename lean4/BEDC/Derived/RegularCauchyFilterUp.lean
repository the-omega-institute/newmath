import BEDC.Derived.RegularCauchyFilterUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RegularCauchyFilterCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont B T (append B T) ∧
      Cont M E (append M E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
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

theorem RegularCauchyFilterCarrier_real_seal_route [AskSetup] [PackageSetup]
    (B R T D M E H C P N : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
      Cont B T (append B T) ∧
      Cont D M (append D M) ∧
      Cont R E (append R E) ∧
      hsame H H ∧
      hsame C C ∧
      hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
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

end BEDC.Derived.RegularCauchyFilterUp
