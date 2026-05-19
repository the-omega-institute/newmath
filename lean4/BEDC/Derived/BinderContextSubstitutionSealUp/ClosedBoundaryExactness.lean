import BEDC.Derived.BinderContextSubstitutionSealUp

namespace BEDC.Derived.BinderContextSubstitutionSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinderContextSubstitutionSealCarrier_closed_boundary_exactness
    [AskSetup] [PackageSetup]
    {term depth payload result boundary transport route provenance name endpoint compiled : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
        provenance name bundle pkg →
      Cont result boundary endpoint →
        Cont payload endpoint compiled →
          hsame endpoint result ∧ hsame compiled transport ∧ UnaryHistory endpoint ∧
            UnaryHistory compiled ∧ Cont payload result transport ∧
              Cont payload endpoint compiled ∧ PkgSig bundle result pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier resultBoundaryEndpoint payloadEndpointCompiled
  obtain ⟨_termUnary, _depthUnary, payloadUnary, resultUnary, boundaryUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _termDepthResult,
    boundaryEmpty, payloadResultTransport, _transportBoundaryRoute, _provenanceResult,
    resultPkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed resultUnary boundaryUnary resultBoundaryEndpoint
  have endpointResult : hsame endpoint result := by
    cases boundaryEmpty
    exact cont_deterministic resultBoundaryEndpoint (cont_right_unit result)
  have compiledTransport : hsame compiled transport :=
    cont_respects_hsame (hsame_refl payload) endpointResult payloadEndpointCompiled
      payloadResultTransport
  have compiledUnary : UnaryHistory compiled :=
    unary_cont_closed payloadUnary endpointUnary payloadEndpointCompiled
  exact
    ⟨endpointResult, compiledTransport, endpointUnary, compiledUnary,
      payloadResultTransport, payloadEndpointCompiled, resultPkg⟩

end BEDC.Derived.BinderContextSubstitutionSealUp
