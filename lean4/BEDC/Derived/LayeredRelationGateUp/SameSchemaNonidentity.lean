import BEDC.Derived.LayeredRelationGateUp.TasteGate

namespace BEDC.Derived.LayeredRelationGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem LayeredRelationGate_same_schema_nonidentity
    (sourceLeft sourceRight layerList preserved notPreserved refusalLedger gateVerdict
      transport continuation provenance : BHist) :
    ∃ packet : LayeredRelationGateUp,
      packet =
          LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved notPreserved
            refusalLedger gateVerdict transport continuation provenance ∧
        List.Mem (layeredRelationGateEncodeBHist preserved)
          (layeredRelationGateToEventFlow packet) ∧
          List.Mem (layeredRelationGateEncodeBHist notPreserved)
            (layeredRelationGateToEventFlow packet) ∧
            LayeredRelationGateUp.mk BHist.Empty (BHist.e0 BHist.Empty) layerList
                preserved notPreserved refusalLedger gateVerdict transport continuation
                provenance ≠
              LayeredRelationGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty layerList
                preserved notPreserved refusalLedger gateVerdict transport continuation
                provenance := by
  -- BEDC touchpoint anchor: BHist BMark
  let packet :=
    LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved notPreserved
      refusalLedger gateVerdict transport continuation provenance
  refine ⟨packet, rfl, ?_, ?_, ?_⟩
  · dsimp [packet, layeredRelationGateToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  · dsimp [packet, layeredRelationGateToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  · intro h
    cases h

end BEDC.Derived.LayeredRelationGateUp
