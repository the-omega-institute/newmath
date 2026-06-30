import BEDC.Derived.TypedGapSocketTaxonomyUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.TypedGapSocketTaxonomyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem TypedGapSocketTaxonomyPublicExport {x : TypedGapSocketTaxonomyUp} :
    ∃ kind gate matrix ledger transport replay provenance localName gateMatrix gateLocal
        publicRead : BHist,
      x = TypedGapSocketTaxonomyUp.mk kind gate matrix ledger transport replay provenance
          localName ∧
        Cont gate matrix gateMatrix ∧
          Cont gate localName gateLocal ∧
            Cont gateMatrix ledger publicRead ∧
              List.Mem (typedGapSocketTaxonomyEncodeBHist kind)
                (typedGapSocketTaxonomyToEventFlow x) ∧
                List.Mem (typedGapSocketTaxonomyEncodeBHist gate)
                  (typedGapSocketTaxonomyToEventFlow x) ∧
                  List.Mem (typedGapSocketTaxonomyEncodeBHist matrix)
                    (typedGapSocketTaxonomyToEventFlow x) ∧
                    List.Mem (typedGapSocketTaxonomyEncodeBHist ledger)
                      (typedGapSocketTaxonomyToEventFlow x) ∧
                      List.Mem (typedGapSocketTaxonomyEncodeBHist localName)
                        (typedGapSocketTaxonomyToEventFlow x) := by
  -- BEDC touchpoint anchor: BHist Cont BMark
  cases x with
  | mk kind gate matrix ledger transport replay provenance localName =>
      let gateMatrix : BHist := append gate matrix
      let gateLocal : BHist := append gate localName
      let publicRead : BHist := append gateMatrix ledger
      refine
        ⟨kind, gate, matrix, ledger, transport, replay, provenance, localName,
          gateMatrix, gateLocal, publicRead, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact cont_intro rfl
      · exact cont_intro rfl
      · exact cont_intro rfl
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _ (List.Mem.head _)))))))

end BEDC.Derived.TypedGapSocketTaxonomyUp
