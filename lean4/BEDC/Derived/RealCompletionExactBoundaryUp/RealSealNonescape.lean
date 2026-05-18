import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem RealCompletionExactBoundaryRealSealNonescape
    (limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
      provenance nameCert : BHist) :
    realCompletionExactBoundaryFields
        (RealCompletionExactBoundaryUp.mk limitSeal classifier witness synchronizer window readback
          dyadic terminal transport replay provenance nameCert) =
      [limitSeal, classifier, witness, synchronizer, window, readback, dyadic, terminal,
        transport, replay, provenance, nameCert] ∧
      realCompletionExactBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
        hsame limitSeal limitSeal ∧ hsame classifier classifier ∧ hsame witness witness ∧
          hsame synchronizer synchronizer ∧ hsame window window ∧ hsame readback readback ∧
            hsame dyadic dyadic ∧ hsame terminal terminal ∧ hsame nameCert nameCert := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  constructor
  · rfl
  · constructor
    · rfl
    · exact
        ⟨hsame_refl limitSeal, hsame_refl classifier, hsame_refl witness,
          hsame_refl synchronizer, hsame_refl window, hsame_refl readback,
          hsame_refl dyadic, hsame_refl terminal, hsame_refl nameCert⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
