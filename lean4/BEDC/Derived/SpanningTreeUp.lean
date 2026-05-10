import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SpanningTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpanningTreeCarrierPacket_dependency_surface [AskSetup] [PackageSetup]
    {vertex graphEdge treeEdge root incidence reachability acyclicity provenance treeLedger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertex ->
      UnaryHistory graphEdge ->
        UnaryHistory treeEdge ->
          UnaryHistory root ->
            UnaryHistory acyclicity ->
              UnaryHistory provenance ->
                Cont graphEdge treeEdge incidence ->
                  Cont root incidence reachability ->
                    Cont reachability acyclicity treeLedger ->
                      Cont provenance treeLedger endpoint ->
                        PkgSig bundle endpoint pkg ->
                          UnaryHistory incidence ∧ UnaryHistory reachability ∧
                            UnaryHistory treeLedger ∧ UnaryHistory endpoint ∧
                              hsame incidence (append graphEdge treeEdge) ∧
                                hsame reachability (append root incidence) ∧
                                  hsame treeLedger (append reachability acyclicity) ∧
                                    hsame endpoint (append provenance treeLedger) ∧
                                      PkgSig bundle endpoint pkg := by
  intro _ graphEdgeUnary treeEdgeUnary rootUnary acyclicityUnary provenanceUnary
  intro edgeIncidence rootReachability reachabilityLedger provenanceEndpoint endpointPkg
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed graphEdgeUnary treeEdgeUnary edgeIncidence
  have reachabilityUnary : UnaryHistory reachability :=
    unary_cont_closed rootUnary incidenceUnary rootReachability
  have ledgerUnary : UnaryHistory treeLedger :=
    unary_cont_closed reachabilityUnary acyclicityUnary reachabilityLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary provenanceEndpoint
  exact And.intro incidenceUnary
    (And.intro reachabilityUnary
      (And.intro ledgerUnary
        (And.intro endpointUnary
          (And.intro edgeIncidence
            (And.intro rootReachability
              (And.intro reachabilityLedger
                (And.intro provenanceEndpoint endpointPkg)))))))

end BEDC.Derived.SpanningTreeUp
