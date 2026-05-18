import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_source_graph_edge_readback [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert
      graphRead edgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg ->
      hsame graphRead graph ->
        Cont source graphRead edgeRead ->
          PkgSig bundle edgeRead pkg ->
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graphRead ∧
              UnaryHistory edgeRead ∧ hsame edgeAdmission edgeRead ∧
                Cont source graphRead edgeRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle cert pkg ∧ PkgSig bundle edgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier sameGraph sourceGraphRead edgePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _edgeUnary, _liftUnary, _transportUnary,
    _routesUnary, _provenanceUnary, _certUnary, sourceGraphEdge, _edgeLiftTarget,
    _transportRoutesProvenance, provenancePkg, certPkg⟩ := carrier
  have graphReadUnary : UnaryHistory graphRead :=
    unary_transport_symm graphUnary sameGraph
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_cont_closed sourceUnary graphReadUnary sourceGraphRead
  have sameEdge : hsame edgeAdmission edgeRead :=
    cont_respects_hsame (hsame_refl source) (hsame_symm sameGraph) sourceGraphEdge
      sourceGraphRead
  exact
    ⟨sourceUnary, targetUnary, graphReadUnary, edgeReadUnary, sameEdge, sourceGraphRead,
      provenancePkg, certPkg, edgePkg⟩

end BEDC.Derived.KernelMorphismUp
