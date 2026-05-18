import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem RealCompletionExactBoundaryStreamNameRegSeq_route
    (limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
      provenance name : BHist) :
    realCompletionExactBoundaryFields
        (RealCompletionExactBoundaryUp.mk limitSeal classifier witness synchronizer window readback
          dyadic terminal transport replay provenance name) =
      [limitSeal, classifier, witness, synchronizer, window, readback, dyadic, terminal,
        transport, replay, provenance, name] ∧
      realCompletionExactBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
        hsame window window ∧ hsame readback readback ∧ hsame dyadic dyadic ∧
          hsame terminal terminal := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  constructor
  · rfl
  · constructor
    · rfl
    · exact
        ⟨hsame_refl window, hsame_refl readback, hsame_refl dyadic, hsame_refl terminal⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
