import BEDC.Derived.BoolUp

namespace BEDC.Derived.BoolUp

theorem BoolUp_StdBridge :
    (∀ h : BEDC.FKernel.Hist.BHist, BoolHistoryCarrier h →
      ∃ v : BEDC.FKernel.Mark.BMark,
        BEDC.FKernel.Hist.hsame h (BoolEndpoint v) ∧ BoolSourceSpec v ∧
          ∀ w : BEDC.FKernel.Mark.BMark,
            BEDC.FKernel.Hist.hsame h (BoolEndpoint w) → BoolClassifierSpec v w) ∧
      (∀ v w : BEDC.FKernel.Mark.BMark,
        BoolClassifierSpec v w ↔
          BEDC.FKernel.Hist.hsame (BoolEndpoint v) (BoolEndpoint w)) ∧
      BoolHistoryCarrier BEDC.FKernel.Hist.BHist.Empty ∧
      BoolHistoryCarrier (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty) ∧
      (∀ h : BEDC.FKernel.Hist.BHist,
        BoolHistoryCarrier (BEDC.FKernel.Hist.BHist.e0 h) → False) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  constructor
  · intro h carrier
    exact BoolEndpoint_readback_total_unique carrier
  · constructor
    · intro v w
      exact BoolEndpoint_bridge_exactness (v := v) (w := w)
    · constructor
      · exact Or.inl
          (BEDC.FKernel.Hist.hsame_refl BEDC.FKernel.Hist.BHist.Empty)
      · constructor
        · exact Or.inr
            (BEDC.FKernel.Hist.hsame_refl
              (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty))
        · intro h carrier
          exact BoolHistoryCarrier_e0_absurd carrier

end BEDC.Derived.BoolUp
