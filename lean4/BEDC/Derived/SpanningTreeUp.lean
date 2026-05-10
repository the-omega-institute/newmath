import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpanningTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

end BEDC.Derived.SpanningTreeUp
