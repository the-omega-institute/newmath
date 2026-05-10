import BEDC.Derived.GraphUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SpanningTreeUp

open BEDC.Derived.GraphUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

end BEDC.Derived.SpanningTreeUp
