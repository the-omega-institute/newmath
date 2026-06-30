import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem CofinalStreamTailSelectorStreamRoute (x : CofinalStreamTailSelectorUp) :
    ∃ precision window regseqHandoff dyadicReadback realSeal selectorProvenance
        hsameTransport contReplay pkgProvenance localName : BHist,
      x =
          CofinalStreamTailSelectorUp.mk precision window regseqHandoff dyadicReadback
            realSeal selectorProvenance hsameTransport contReplay pkgProvenance
            localName ∧
        cofinalStreamTailSelectorToEventFlow x =
          [[BMark.b0],
            cofinalStreamTailSelectorEncodeBHist precision,
            [BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist window,
            [BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist regseqHandoff,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist dyadicReadback,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist realSeal,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist selectorProvenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            cofinalStreamTailSelectorEncodeBHist hsameTransport,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist contReplay,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist pkgProvenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist localName] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk precision window regseqHandoff dyadicReadback realSeal selectorProvenance
      hsameTransport contReplay pkgProvenance localName =>
      refine
        ⟨precision, window, regseqHandoff, dyadicReadback, realSeal,
          selectorProvenance, hsameTransport, contReplay, pkgProvenance,
          localName, ?_⟩
      constructor
      · rfl
      · rfl

end BEDC.Derived.CofinalStreamTailSelectorUp
