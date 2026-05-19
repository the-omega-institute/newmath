import BEDC.Derived.BinderContextSubstitutionSealUp

namespace BEDC.Derived.BinderContextSubstitutionSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinderContextSubstitutionSealCarrier_obligation_consumer [AskSetup] [PackageSetup]
    {term depth payload result boundary transport route provenance name endpoint compiled audit :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
        provenance name bundle pkg ->
      Cont result boundary endpoint ->
        Cont payload endpoint compiled ->
          Cont compiled provenance audit ->
            PkgSig bundle endpoint pkg ->
              PkgSig bundle compiled pkg ->
                PkgSig bundle audit pkg ->
                  hsame endpoint result ∧ UnaryHistory term ∧ UnaryHistory payload ∧
                    UnaryHistory endpoint ∧ UnaryHistory compiled ∧ UnaryHistory audit ∧
                      Cont term depth result ∧ Cont result boundary endpoint ∧
                        Cont payload endpoint compiled ∧ Cont compiled provenance audit ∧
                          PkgSig bundle result pkg ∧ PkgSig bundle endpoint pkg ∧
                            PkgSig bundle compiled pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier resultBoundaryEndpoint payloadEndpointCompiled compiledProvenanceAudit
    endpointPkg compiledPkg auditPkg
  obtain ⟨termUnary, _depthUnary, payloadUnary, resultUnary, boundaryUnary, _transportUnary,
    _routeUnary, provenanceUnary, _nameUnary, termDepthResult, boundaryEmpty,
    _payloadResultTransport, _transportBoundaryRoute, _provenanceResult, resultPkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed resultUnary boundaryUnary resultBoundaryEndpoint
  have endpointResult : hsame endpoint result := by
    cases boundaryEmpty
    exact cont_deterministic resultBoundaryEndpoint (cont_right_unit result)
  have compiledUnary : UnaryHistory compiled :=
    unary_cont_closed payloadUnary endpointUnary payloadEndpointCompiled
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed compiledUnary provenanceUnary compiledProvenanceAudit
  exact
    ⟨endpointResult, termUnary, payloadUnary, endpointUnary, compiledUnary, auditUnary,
      termDepthResult, resultBoundaryEndpoint, payloadEndpointCompiled, compiledProvenanceAudit,
      resultPkg, endpointPkg, compiledPkg, auditPkg⟩

end BEDC.Derived.BinderContextSubstitutionSealUp
