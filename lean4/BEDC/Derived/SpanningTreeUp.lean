import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpanningTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

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

end BEDC.Derived.SpanningTreeUp
