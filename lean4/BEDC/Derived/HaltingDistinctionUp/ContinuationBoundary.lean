import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionContinuationBoundary [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead diagonalRead
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont trace route traceRead ->
        Cont traceRead diagonal diagonalRead ->
          Cont diagonalRead cert endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory traceRead ∧ UnaryHistory diagonalRead ∧ UnaryHistory endpoint ∧
                Cont trace route traceRead ∧ Cont traceRead diagonal diagonalRead ∧
                  Cont diagonalRead cert endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier traceRouteRead traceReadDiagonalRead diagonalReadCertEndpoint endpointPkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed traceReadUnary diagonalUnary traceReadDiagonalRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed diagonalReadUnary certUnary diagonalReadCertEndpoint
  exact
    ⟨traceReadUnary, diagonalReadUnary, endpointUnary, traceRouteRead,
      traceReadDiagonalRead, diagonalReadCertEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionUp
