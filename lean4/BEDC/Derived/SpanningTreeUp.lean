import BEDC.Derived.GraphUp
import BEDC.Derived.TreeUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SpanningTreeUp

open BEDC.Derived.GraphUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.Derived.TreeUp

def SpanningTreeCarrierPacket [AskSetup] [PackageSetup]
    (vertices graphEdges treeEdges root incidence reachability acyclic graphPkg treePkg
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vertices ∧ UnaryHistory graphEdges ∧ UnaryHistory treeEdges ∧
    UnaryHistory root ∧ UnaryHistory incidence ∧ UnaryHistory reachability ∧
      UnaryHistory acyclic ∧ Cont graphPkg treePkg provenance ∧
        Cont provenance acyclic endpoint ∧ PkgSig bundle endpoint pkg

theorem SpanningTreeCarrierPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {vertices graphEdges treeEdges root incidence reachability acyclic graphPkg treePkg
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpanningTreeCarrierPacket vertices graphEdges treeEdges root incidence reachability acyclic
        graphPkg treePkg provenance endpoint bundle pkg ->
      UnaryHistory vertices ∧ UnaryHistory graphEdges ∧ UnaryHistory treeEdges ∧
        UnaryHistory root ∧ UnaryHistory incidence ∧ UnaryHistory reachability ∧
          UnaryHistory acyclic ∧ Cont graphPkg treePkg provenance ∧
            Cont provenance acyclic endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  obtain ⟨verticesUnary, graphEdgesUnary, treeEdgesUnary, rootUnary, incidenceUnary,
    reachabilityUnary, acyclicUnary, provenanceCont, endpointCont, pkgSig⟩ := packet
  exact
    ⟨verticesUnary, graphEdgesUnary, treeEdgesUnary, rootUnary, incidenceUnary,
      reachabilityUnary, acyclicUnary, provenanceCont, endpointCont, pkgSig⟩

def SpanningTreeBHistCarrier [AskSetup] [PackageSetup]
    (graph tree incidence reachability acyclic provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  GraphContEdge graph tree incidence ∧ UnaryHistory reachability ∧
    hsame acyclic BHist.Empty ∧ Cont incidence reachability acyclic ∧
      Cont acyclic provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem SpanningTreeBHistCarrier_classifier_obligation [AskSetup] [PackageSetup]
    {graph tree incidence reachability acyclic provenance endpoint graph' tree' incidence'
      reachability' acyclic' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpanningTreeBHistCarrier graph tree incidence reachability acyclic provenance endpoint
        bundle pkg ->
      hsame graph graph' ->
      hsame tree tree' ->
      hsame reachability reachability' ->
      hsame acyclic acyclic' ->
      hsame provenance provenance' ->
      Cont graph' tree' incidence' ->
      Cont incidence' reachability' acyclic' ->
      Cont acyclic' provenance' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      SpanningTreeBHistCarrier graph' tree' incidence' reachability' acyclic' provenance'
          endpoint' bundle pkg ∧
        hsame incidence incidence' ∧ hsame endpoint endpoint' := by
  intro carrier sameGraph sameTree sameReachability sameAcyclic sameProvenance incidenceCont'
    acyclicCont' endpointCont' pkgSig'
  have sameIncidence : hsame incidence incidence' :=
    cont_respects_hsame sameGraph sameTree carrier.left.right.right incidenceCont'
  have graphEdge' : GraphContEdge graph' tree' incidence' :=
    (GraphContEdge_classifier_transport carrier.left sameGraph sameTree sameIncidence).left
  have reachabilityUnary' : UnaryHistory reachability' :=
    unary_transport carrier.right.left sameReachability
  have acyclicEmpty' : hsame acyclic' BHist.Empty :=
    hsame_trans (hsame_symm sameAcyclic) carrier.right.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameAcyclic sameProvenance carrier.right.right.right.right.left
      endpointCont'
  exact
    ⟨⟨graphEdge',
        reachabilityUnary',
        acyclicEmpty',
        acyclicCont',
        endpointCont',
        pkgSig'⟩,
      sameIncidence,
      sameEndpoint⟩

theorem SpanningTreeAcyclicMaximality_surface [AskSetup] [PackageSetup]
    {graph tree incidence reachability acyclic provenance endpoint maximality : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpanningTreeBHistCarrier graph tree incidence reachability acyclic provenance endpoint
        bundle pkg ->
      Cont reachability acyclic maximality ->
        UnaryHistory maximality ∧ hsame maximality (append reachability acyclic) ∧
          hsame acyclic BHist.Empty ∧ hsame endpoint (append acyclic provenance) ∧
            PkgSig bundle endpoint pkg := by
  intro carrier maximalityCont
  have acyclicUnary : UnaryHistory acyclic :=
    unary_transport unary_empty (hsame_symm carrier.right.right.left)
  have maximalityUnary : UnaryHistory maximality :=
    unary_cont_closed carrier.right.left acyclicUnary maximalityCont
  exact
    ⟨maximalityUnary,
      maximalityCont,
      carrier.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right⟩

theorem SpanningTreeCarrier_obligation_surface [AskSetup] [PackageSetup]
    {graphEdges treeEdges incidence reachability provenance carrierRow : BHist}
    {graphBundle treeBundle : ProbeBundle ProbeName} {graphPkg treePkg : Pkg} :
    UnaryHistory graphEdges -> UnaryHistory treeEdges -> UnaryHistory incidence ->
      UnaryHistory reachability -> PkgSig graphBundle graphEdges graphPkg ->
        PkgSig treeBundle treeEdges treePkg -> Cont graphEdges treeEdges carrierRow ->
          Cont incidence reachability provenance ->
            UnaryHistory carrierRow ∧ hsame carrierRow (append graphEdges treeEdges) ∧
              Cont incidence reachability provenance ∧ PkgSig graphBundle graphEdges graphPkg ∧
                PkgSig treeBundle treeEdges treePkg := by
  intro graphUnary treeUnary _incidenceUnary _reachabilityUnary graphPkgSig treePkgSig carrierCont
  intro provenanceCont
  have carrierUnary : UnaryHistory carrierRow :=
    unary_cont_closed graphUnary treeUnary carrierCont
  exact ⟨carrierUnary, carrierCont, provenanceCont, graphPkgSig, treePkgSig⟩

theorem SpanningTreeClassifier_obligation_surface [AskSetup] [PackageSetup]
    {graphEdges graphEdges' treeEdges treeEdges' incidence incidence' reachability reachability'
      acyclicity acyclicity' carrierRow carrierRow' provenance provenance' : BHist} :
    Cont graphEdges treeEdges carrierRow -> Cont graphEdges' treeEdges' carrierRow' ->
      hsame graphEdges graphEdges' -> hsame treeEdges treeEdges' ->
        hsame incidence incidence' -> hsame reachability reachability' ->
          hsame acyclicity acyclicity' -> Cont incidence reachability provenance ->
            Cont incidence' reachability' provenance' ->
              hsame carrierRow carrierRow' ∧ hsame provenance provenance' := by
  intro carrierCont carrierCont' sameGraphEdges sameTreeEdges sameIncidence sameReachability
  intro _sameAcyclicity provenanceCont provenanceCont'
  have sameCarrier : hsame carrierRow carrierRow' :=
    cont_respects_hsame sameGraphEdges sameTreeEdges carrierCont carrierCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameIncidence sameReachability provenanceCont provenanceCont'
  exact ⟨sameCarrier, sameProvenance⟩

theorem SpanningTreeClassifier_transport_surface
    {graph edge connected acyclic root endpoint endpoint' root' connected' acyclic' :
      BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      hsame endpoint endpoint' ->
        hsame root root' ->
          hsame connected connected' ->
            hsame acyclic acyclic' ->
              GraphContEdge graph edge connected' ∧ TreeRootBranch endpoint' root' connected' ∧
                UnaryHistory acyclic' ∧ Cont endpoint' root' connected' := by
  intro carrier sameEndpoint sameRoot sameConnected sameAcyclic
  have transported :
      TreeBHistCarrier graph edge connected' acyclic' root' endpoint' ∧
        GraphContEdge endpoint' root' connected' ∧ UnaryHistory acyclic' ∧
          Cont endpoint' root' connected' :=
    TreeBHistCarrier_stability_ledger_transport
      carrier sameEndpoint sameRoot sameConnected sameAcyclic
  exact And.intro transported.left.left
    (And.intro transported.left.right.right
      (And.intro transported.right.right.left transported.right.right.right))

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

theorem SpanningTreeAcyclicMaximality_obligation_surface
    {treeEdge incidence root reachability acyclicity candidate ledger : BHist} :
    UnaryHistory treeEdge -> UnaryHistory incidence -> UnaryHistory root ->
      UnaryHistory acyclicity -> Cont root incidence reachability ->
        Cont treeEdge reachability candidate -> Cont candidate acyclicity ledger ->
          UnaryHistory reachability ∧ UnaryHistory candidate ∧ UnaryHistory ledger ∧
            hsame reachability (append root incidence) ∧
              hsame candidate (append treeEdge reachability) ∧
                hsame ledger (append candidate acyclicity) := by
  intro treeEdgeUnary incidenceUnary rootUnary acyclicityUnary rootIncidence
  intro treeReachability candidateAcyclicity
  have reachabilityUnary : UnaryHistory reachability :=
    unary_cont_closed rootUnary incidenceUnary rootIncidence
  have candidateUnary : UnaryHistory candidate :=
    unary_cont_closed treeEdgeUnary reachabilityUnary treeReachability
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed candidateUnary acyclicityUnary candidateAcyclicity
  exact And.intro reachabilityUnary
    (And.intro candidateUnary
      (And.intro ledgerUnary
        (And.intro rootIncidence
          (And.intro treeReachability candidateAcyclicity))))

theorem SpanningTreeCarrierPacket_classifier_obligation [AskSetup] [PackageSetup]
    {vertex graphEdge treeEdge root incidence reachability acyclicity provenance treeLedger
      endpoint classifier : BHist}
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
                        Cont endpoint acyclicity classifier ->
                          PkgSig bundle endpoint pkg ->
                            UnaryHistory incidence ∧ UnaryHistory reachability ∧
                              UnaryHistory treeLedger ∧ UnaryHistory endpoint ∧
                                UnaryHistory classifier ∧
                                  hsame incidence (append graphEdge treeEdge) ∧
                                    hsame reachability (append root incidence) ∧
                                      hsame treeLedger (append reachability acyclicity) ∧
                                        hsame endpoint (append provenance treeLedger) ∧
                                          hsame classifier (append endpoint acyclicity) ∧
                                            PkgSig bundle endpoint pkg := by
  intro _ graphEdgeUnary treeEdgeUnary rootUnary acyclicityUnary provenanceUnary
  intro edgeIncidence rootReachability reachabilityLedger provenanceEndpoint endpointClassifier
  intro endpointPkg
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed graphEdgeUnary treeEdgeUnary edgeIncidence
  have reachabilityUnary : UnaryHistory reachability :=
    unary_cont_closed rootUnary incidenceUnary rootReachability
  have ledgerUnary : UnaryHistory treeLedger :=
    unary_cont_closed reachabilityUnary acyclicityUnary reachabilityLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary provenanceEndpoint
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed endpointUnary acyclicityUnary endpointClassifier
  exact
    ⟨incidenceUnary, reachabilityUnary, ledgerUnary, endpointUnary, classifierUnary,
      edgeIncidence, rootReachability, reachabilityLedger, provenanceEndpoint, endpointClassifier,
      endpointPkg⟩

theorem SpanningTreeCarrierPacket_incidence_reachability_transport [AskSetup] [PackageSetup]
    {vertex vertex' graphEdge graphEdge' treeEdge treeEdge' root root' incidence incidence'
      reachability reachability' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertex ->
      UnaryHistory graphEdge ->
        UnaryHistory treeEdge ->
          UnaryHistory root ->
            hsame vertex vertex' ->
              hsame graphEdge graphEdge' ->
                hsame treeEdge treeEdge' ->
                  hsame root root' ->
                    Cont graphEdge treeEdge incidence ->
                      Cont graphEdge' treeEdge' incidence' ->
                        Cont root incidence reachability ->
                          Cont root' incidence' reachability' ->
                            Cont vertex reachability endpoint ->
                              Cont vertex' reachability' endpoint' ->
                                PkgSig bundle endpoint pkg ->
                                  UnaryHistory incidence' ∧ UnaryHistory reachability' ∧
                                    UnaryHistory endpoint' ∧ hsame incidence incidence' ∧
                                      hsame reachability reachability' ∧
                                        hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg := by
  intro vertexUnary graphEdgeUnary treeEdgeUnary rootUnary sameVertex sameGraphEdge
  intro sameTreeEdge sameRoot leftIncidence rightIncidence leftReachability
  intro rightReachability leftEndpoint rightEndpoint endpointPkg
  have graphEdgeUnary' : UnaryHistory graphEdge' :=
    unary_transport graphEdgeUnary sameGraphEdge
  have treeEdgeUnary' : UnaryHistory treeEdge' :=
    unary_transport treeEdgeUnary sameTreeEdge
  have rootUnary' : UnaryHistory root' :=
    unary_transport rootUnary sameRoot
  have incidenceUnary' : UnaryHistory incidence' :=
    unary_cont_closed graphEdgeUnary' treeEdgeUnary' rightIncidence
  have reachabilityUnary' : UnaryHistory reachability' :=
    unary_cont_closed rootUnary' incidenceUnary' rightReachability
  have vertexUnary' : UnaryHistory vertex' :=
    unary_transport vertexUnary sameVertex
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed vertexUnary' reachabilityUnary' rightEndpoint
  have sameIncidence : hsame incidence incidence' :=
    cont_respects_hsame sameGraphEdge sameTreeEdge leftIncidence rightIncidence
  have sameReachability : hsame reachability reachability' :=
    cont_respects_hsame sameRoot sameIncidence leftReachability rightReachability
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameVertex sameReachability leftEndpoint rightEndpoint
  exact And.intro incidenceUnary'
    (And.intro reachabilityUnary'
      (And.intro endpointUnary'
        (And.intro sameIncidence
          (And.intro sameReachability (And.intro sameEndpoint endpointPkg)))))

def SpanningTreeCarrier [AskSetup] [PackageSetup]
    (vertices graphEdges treeEdges root incidence reach acyclic endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vertices ∧ UnaryHistory graphEdges ∧ UnaryHistory treeEdges ∧
    UnaryHistory root ∧ Cont vertices graphEdges incidence ∧ Cont root treeEdges reach ∧
      Cont treeEdges reach acyclic ∧ Cont acyclic incidence endpoint ∧
        PkgSig bundle endpoint pkg

theorem SpanningTreeCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {vertices graphEdges treeEdges root incidence reach acyclic endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpanningTreeCarrier vertices graphEdges treeEdges root incidence reach acyclic endpoint
        bundle pkg ->
      SemanticNameCert
        (SpanningTreeCarrier vertices graphEdges treeEdges root incidence reach acyclic ·
          bundle pkg)
        (SpanningTreeCarrier vertices graphEdges treeEdges root incidence reach acyclic ·
          bundle pkg)
        (SpanningTreeCarrier vertices graphEdges treeEdges root incidence reach acyclic ·
          bundle pkg)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint carrier
      equiv_refl := by
        intro row _carrierRow
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases sameRows
        exact carrierRow
    }
    pattern_sound := by
      intro _row carrierRow
      exact carrierRow
    ledger_sound := by
      intro _row carrierRow
      exact carrierRow
  }

theorem SpanningTreeCarrierSurface_carrier_obligation [AskSetup] [PackageSetup]
    {vertex graphEdge treeEdge root incidence reachability acyclicity ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont vertex graphEdge incidence ->
      Cont treeEdge root reachability ->
        Cont incidence reachability ledger ->
          Cont ledger acyclicity endpoint ->
            PkgSig bundle endpoint pkg ->
              hsame incidence (append vertex graphEdge) ∧
                hsame reachability (append treeEdge root) ∧
                  hsame ledger (append incidence reachability) ∧
                    hsame endpoint (append ledger acyclicity) ∧
                      PkgSig bundle endpoint pkg := by
  intro incidenceRow reachabilityRow ledgerRow endpointRow pkgSig
  exact And.intro incidenceRow
    (And.intro reachabilityRow
      (And.intro ledgerRow
        (And.intro endpointRow pkgSig)))

end BEDC.Derived.SpanningTreeUp
