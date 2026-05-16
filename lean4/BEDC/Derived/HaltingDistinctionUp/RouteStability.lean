import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionCarrier_route_stability [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert routeRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont classifier route routeRead →
        Cont routeRead cert endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory classifier ∧ UnaryHistory route ∧ UnaryHistory routeRead ∧
              UnaryHistory endpoint ∧ Cont classifier route routeRead ∧
                Cont routeRead cert endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier classifierRouteRead routeCertEndpoint endpointPkg
  obtain ⟨_questionUnary, _traceUnary, _diagonalUnary, _haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeReadUnary certUnary routeCertEndpoint
  exact
    ⟨classifierUnary, routeUnary, routeReadUnary, endpointUnary, classifierRouteRead,
      routeCertEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionUp
