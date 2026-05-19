import BEDC.Derived.BinderContextSubstitutionSealUp

namespace BEDC.Derived.BinderContextSubstitutionSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinderContextSubstitutionSealCarrier_closed_term_boundary_dependency
    [AskSetup] [PackageSetup]
    {term depth payload result boundary transport route provenance name endpoint dependency : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
        provenance name bundle pkg →
      Cont result boundary endpoint →
        Cont boundary provenance dependency →
          PkgSig bundle endpoint pkg →
            PkgSig bundle dependency pkg →
              hsame endpoint result ∧ UnaryHistory boundary ∧ UnaryHistory dependency ∧
                Cont result boundary endpoint ∧ Cont boundary provenance dependency ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle dependency pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier resultBoundaryEndpoint boundaryProvenanceDependency endpointPkg dependencyPkg
  obtain ⟨_termUnary, _depthUnary, _payloadUnary, resultUnary, boundaryUnary,
    _transportUnary, _routeUnary, provenanceUnary, _nameUnary, _termDepthResult,
    boundaryEmpty, _payloadResultTransport, _transportBoundaryRoute, _provenanceResult,
    _resultPkg⟩ := carrier
  have endpointResult : hsame endpoint result := by
    cases boundaryEmpty
    exact cont_deterministic resultBoundaryEndpoint (cont_right_unit result)
  have dependencyUnary : UnaryHistory dependency :=
    unary_cont_closed boundaryUnary provenanceUnary boundaryProvenanceDependency
  exact
    ⟨endpointResult, boundaryUnary, dependencyUnary, resultBoundaryEndpoint,
      boundaryProvenanceDependency, endpointPkg, dependencyPkg⟩

end BEDC.Derived.BinderContextSubstitutionSealUp
