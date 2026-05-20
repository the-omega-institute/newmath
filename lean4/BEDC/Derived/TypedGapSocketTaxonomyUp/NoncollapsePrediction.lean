import BEDC.Derived.TypedGapSocketTaxonomyUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.TypedGapSocketTaxonomyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem TypedGapSocketTaxonomyNoncollapsePrediction {x : TypedGapSocketTaxonomyUp} :
    ∃ kind gate matrix siblingLedger transport replay provenance localName gateMatrix gateLocal :
      BHist,
      x = TypedGapSocketTaxonomyUp.mk kind gate matrix siblingLedger transport replay provenance
          localName ∧
        Cont gate matrix gateMatrix ∧
          Cont gate localName gateLocal ∧
            List.Mem (typedGapSocketTaxonomyEncodeBHist gate)
              (typedGapSocketTaxonomyToEventFlow x) ∧
              List.Mem (typedGapSocketTaxonomyEncodeBHist matrix)
                (typedGapSocketTaxonomyToEventFlow x) := by
  -- BEDC touchpoint anchor: BHist Cont
  cases x with
  | mk kind gate matrix siblingLedger transport replay provenance localName =>
      exact
        ⟨kind, gate, matrix, siblingLedger, transport, replay, provenance, localName,
          append gate matrix, append gate localName, rfl, rfl, rfl, by
            exact List.Mem.tail _ (List.Mem.head _), by
            exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))⟩

end BEDC.Derived.TypedGapSocketTaxonomyUp
