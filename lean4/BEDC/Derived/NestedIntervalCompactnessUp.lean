import BEDC.Derived.NestedIntervalCompactnessUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.NestedIntervalCompactnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem NestedIntervalCompactnessCarrier_namecert_obligations
    (I L D W R E H C P N : BHist) :
    nestedIntervalCompactnessFromEventFlow
          (nestedIntervalCompactnessToEventFlow
            (NestedIntervalCompactnessUp.mk I L D W R E H C P N)) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N) ∧
      nestedIntervalCompactnessFields
          (NestedIntervalCompactnessUp.mk I L D W R E H C P N) =
        [I, L, D, W, R, E, H, C, P, N] ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist I))
          I ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist D))
          D ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist E))
          E ∧
      Cont I D (append I D) ∧
      Cont D W (append D W) ∧
      Cont W R (append W R) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist,
        nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [nestedIntervalCompactnessToEventFlow, nestedIntervalCompactnessFromEventFlow]
    change
      some
          (NestedIntervalCompactnessUp.mk
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist I))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist L))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist D))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist R))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist E))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist H))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist C))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist P))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist N))) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N)
    rw [hdecode I, hdecode L, hdecode D, hdecode W, hdecode R, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · exact hdecode I
      · constructor
        · exact hdecode D
        · constructor
          · exact hdecode E
          · constructor
            · rfl
            · constructor
              · rfl
              · rfl

theorem NestedIntervalCompactnessCarrier_located_endpoint_scope
    (I L D W R E H C P N : BHist) :
    nestedIntervalCompactnessFromEventFlow
          (nestedIntervalCompactnessToEventFlow
            (NestedIntervalCompactnessUp.mk I L D W R E H C P N)) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N) ∧
      nestedIntervalCompactnessFields
          (NestedIntervalCompactnessUp.mk I L D W R E H C P N) =
        [I, L, D, W, R, E, H, C, P, N] ∧
      hsame
          (nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist L))
          L ∧
      Cont I L (append I L) ∧
      Cont L D (append L D) ∧
      Cont D W (append D W) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  have hdecode :
      ∀ h : BHist,
        nestedIntervalCompactnessDecodeBHist
            (nestedIntervalCompactnessEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · rw [nestedIntervalCompactnessToEventFlow, nestedIntervalCompactnessFromEventFlow]
    change
      some
          (NestedIntervalCompactnessUp.mk
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist I))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist L))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist D))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist R))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist E))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist H))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist C))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist P))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist N))) =
        some (NestedIntervalCompactnessUp.mk I L D W R E H C P N)
    rw [hdecode I, hdecode L, hdecode D, hdecode W, hdecode R, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  · constructor
    · rfl
    · constructor
      · exact hdecode L
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

end BEDC.Derived.NestedIntervalCompactnessUp
