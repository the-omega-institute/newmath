import BEDC.Derived.PhysicalLawBridgeUp.TasteGate

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem PhysicalLawBridgeNontrivialObligation :
    let lawBranch :=
      PhysicalLawBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    let refusalBranch :=
      PhysicalLawBridgeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    lawBranch ≠ refusalBranch ∧
      BHistCarrier.toEventFlow lawBranch ≠ BHistCarrier.toEventFlow refusalBranch := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier PhysicalLawBridgeUp
  constructor
  · intro h
    cases h
  · intro heq
    have hneq :
        (PhysicalLawBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) ≠
          (PhysicalLawBridgeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) := by
      intro h
      cases h
    exact ChapterTasteGate.layer_separation _ _ hneq heq

end BEDC.Derived.PhysicalLawBridgeUp
