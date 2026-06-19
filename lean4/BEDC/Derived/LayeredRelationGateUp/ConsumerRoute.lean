import BEDC.Derived.LayeredRelationGateUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LayeredRelationGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LayeredRelationGate_consumer_route [AskSetup] [PackageSetup]
    {sourceLeft sourceRight layerList preserved notPreserved refusalLedger gateVerdict transport
      continuation provenance consumer : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory sourceLeft -> UnaryHistory sourceRight -> UnaryHistory layerList ->
      UnaryHistory preserved -> UnaryHistory refusalLedger -> UnaryHistory gateVerdict ->
        UnaryHistory provenance -> Cont sourceLeft sourceRight layerList ->
          Cont layerList preserved notPreserved -> Cont refusalLedger gateVerdict continuation ->
            Cont continuation provenance consumer -> PkgSig bundle provenance pkg ->
              UnaryHistory consumer ∧
                List.Mem (layeredRelationGateEncodeBHist sourceLeft)
                  (layeredRelationGateToEventFlow
                    (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved
                      notPreserved refusalLedger gateVerdict transport continuation provenance)) ∧
                List.Mem (layeredRelationGateEncodeBHist layerList)
                  (layeredRelationGateToEventFlow
                    (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved
                      notPreserved refusalLedger gateVerdict transport continuation provenance)) ∧
                List.Mem (layeredRelationGateEncodeBHist notPreserved)
                  (layeredRelationGateToEventFlow
                    (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved
                      notPreserved refusalLedger gateVerdict transport continuation provenance)) ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig List.Mem
  intro sourceLeftUnary sourceRightUnary _layerListUnary preservedUnary refusalLedgerUnary
    gateVerdictUnary provenanceUnary sourceRoute layerRoute continuationRoute consumerRoute
    provenancePkg
  have layerListFromSource : UnaryHistory layerList :=
    unary_cont_closed sourceLeftUnary sourceRightUnary sourceRoute
  have _notPreservedUnary : UnaryHistory notPreserved :=
    unary_cont_closed layerListFromSource preservedUnary layerRoute
  have continuationUnary : UnaryHistory continuation :=
    unary_cont_closed refusalLedgerUnary gateVerdictUnary continuationRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed continuationUnary provenanceUnary consumerRoute
  have sourceListed :
      List.Mem (layeredRelationGateEncodeBHist sourceLeft)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved
            notPreserved refusalLedger gateVerdict transport continuation provenance)) := by
    change
      List.Mem (layeredRelationGateEncodeBHist sourceLeft)
        [[BMark.b0], layeredRelationGateEncodeBHist sourceLeft, [BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist sourceRight, [BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist layerList,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist preserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist notPreserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist refusalLedger,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          layeredRelationGateEncodeBHist gateVerdict,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist provenance]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have layerListed :
      List.Mem (layeredRelationGateEncodeBHist layerList)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved
            notPreserved refusalLedger gateVerdict transport continuation provenance)) := by
    change
      List.Mem (layeredRelationGateEncodeBHist layerList)
        [[BMark.b0], layeredRelationGateEncodeBHist sourceLeft, [BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist sourceRight, [BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist layerList,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist preserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist notPreserved,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist refusalLedger,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          layeredRelationGateEncodeBHist gateVerdict,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist provenance]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))
  have notPreservedListed :
      List.Mem (layeredRelationGateEncodeBHist notPreserved)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved
            notPreserved refusalLedger gateVerdict transport continuation provenance)) := by
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
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          layeredRelationGateEncodeBHist gateVerdict,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist continuation,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          layeredRelationGateEncodeBHist provenance]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self))))))))
  exact ⟨consumerUnary, sourceListed, layerListed, notPreservedListed, provenancePkg⟩

end BEDC.Derived.LayeredRelationGateUp
