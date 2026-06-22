import BEDC.Derived.LayeredRelationGateUp.ConsumerRoute

namespace BEDC.Derived.LayeredRelationGateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

theorem LayeredRelationGateClassifier_obligation
    {sourceLeft sourceRight layerList preserved notPreserved refusalLedger gateVerdict transport
      continuation provenance verdictRead consumerRead : BHist} :
    UnaryHistory preserved →
      UnaryHistory notPreserved →
        UnaryHistory refusalLedger →
          UnaryHistory gateVerdict →
            Cont preserved notPreserved verdictRead →
              Cont refusalLedger verdictRead consumerRead →
                hsame gateVerdict verdictRead →
                  UnaryHistory verdictRead ∧ UnaryHistory consumerRead ∧
                    hsame gateVerdict verdictRead ∧ Cont preserved notPreserved verdictRead ∧
                      Cont refusalLedger verdictRead consumerRead ∧
                        List.Mem (layeredRelationGateEncodeBHist preserved)
                          (layeredRelationGateToEventFlow
                            (LayeredRelationGateUp.mk sourceLeft sourceRight layerList
                              preserved notPreserved refusalLedger gateVerdict transport
                              continuation provenance)) ∧
                          List.Mem (layeredRelationGateEncodeBHist notPreserved)
                            (layeredRelationGateToEventFlow
                              (LayeredRelationGateUp.mk sourceLeft sourceRight layerList
                                preserved notPreserved refusalLedger gateVerdict transport
                                continuation provenance)) ∧
                            List.Mem (layeredRelationGateEncodeBHist refusalLedger)
                              (layeredRelationGateToEventFlow
                                (LayeredRelationGateUp.mk sourceLeft sourceRight layerList
                                  preserved notPreserved refusalLedger gateVerdict transport
                                  continuation provenance)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory List.Mem
  intro preservedUnary notPreservedUnary refusalLedgerUnary _gateVerdictUnary verdictRoute
    consumerRoute sameVerdict
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed preservedUnary notPreservedUnary verdictRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed refusalLedgerUnary verdictUnary consumerRoute
  have preservedListed :
      List.Mem (layeredRelationGateEncodeBHist preserved)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved notPreserved
            refusalLedger gateVerdict transport continuation provenance)) := by
    change
      List.Mem (layeredRelationGateEncodeBHist preserved)
        [[BMark.b0], layeredRelationGateEncodeBHist sourceLeft, [BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist sourceRight, [BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist layerList,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist preserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist notPreserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist refusalLedger,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist gateVerdict,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          layeredRelationGateEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist provenance]
    repeat first | exact List.mem_cons_self | apply List.mem_cons_of_mem
  have notPreservedListed :
      List.Mem (layeredRelationGateEncodeBHist notPreserved)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved notPreserved
            refusalLedger gateVerdict transport continuation provenance)) := by
    change
      List.Mem (layeredRelationGateEncodeBHist notPreserved)
        [[BMark.b0], layeredRelationGateEncodeBHist sourceLeft, [BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist sourceRight, [BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist layerList,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist preserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist notPreserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist refusalLedger,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist gateVerdict,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          layeredRelationGateEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist provenance]
    repeat first | exact List.mem_cons_self | apply List.mem_cons_of_mem
  have refusalListed :
      List.Mem (layeredRelationGateEncodeBHist refusalLedger)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved notPreserved
            refusalLedger gateVerdict transport continuation provenance)) := by
    change
      List.Mem (layeredRelationGateEncodeBHist refusalLedger)
        [[BMark.b0], layeredRelationGateEncodeBHist sourceLeft, [BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist sourceRight, [BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist layerList,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist preserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist notPreserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist refusalLedger,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist gateVerdict,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          layeredRelationGateEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist provenance]
    repeat first | exact List.mem_cons_self | apply List.mem_cons_of_mem
  exact
    ⟨verdictUnary, consumerUnary, sameVerdict, verdictRoute, consumerRoute, preservedListed,
      notPreservedListed, refusalListed⟩

end BEDC.Derived.LayeredRelationGateUp
