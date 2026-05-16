import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionObstructionConsumerBoundary [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert obstructionRead endpoint
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont classifier route obstructionRead ->
        Cont obstructionRead diagonal endpoint ->
          Cont endpoint route consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
                UnaryHistory route ∧ UnaryHistory obstructionRead ∧ UnaryHistory endpoint ∧
                  UnaryHistory consumerRead ∧ Cont classifier route obstructionRead ∧
                    Cont obstructionRead diagonal endpoint ∧ Cont endpoint route consumerRead ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier classifierRouteObstruction obstructionDiagonalEndpoint endpointRouteConsumer
    consumerPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, _haltUnary, classifierUnary, routeUnary,
    _provenanceUnary, _certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteObstruction
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed obstructionUnary diagonalUnary obstructionDiagonalEndpoint
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary routeUnary endpointRouteConsumer
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, routeUnary, obstructionUnary, endpointUnary,
      consumerUnary, classifierRouteObstruction, obstructionDiagonalEndpoint,
      endpointRouteConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.HaltingDistinctionUp
