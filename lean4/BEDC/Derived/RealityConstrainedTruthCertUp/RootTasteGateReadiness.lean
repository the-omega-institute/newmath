import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem RealityConstrainedTruthCertRootNontrivialReadiness :
    exists x y : TasteGate.RealityConstrainedTruthCertUp,
      x ≠ y /\ BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y := by
  -- BEDC touchpoint anchor: BHist BMark
  let x :=
    TasteGate.RealityConstrainedTruthCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  let y :=
    TasteGate.RealityConstrainedTruthCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  have hxy : x ≠ y := by
    intro h
    have hsource : BHist.Empty = BHist.e0 BHist.Empty := by
      injection h with hsource _ _ _ _ _ _ _ _ _
    cases hsource
  have hflow : BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y :=
    ChapterTasteGate.layer_separation x y hxy
  exact ⟨x, y, hxy, hflow⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
