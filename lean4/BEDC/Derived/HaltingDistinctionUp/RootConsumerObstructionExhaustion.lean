import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionCarrier_root_consumer_obstruction_exhaustion
    [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert obstructionRead endpoint
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont classifier route obstructionRead →
        Cont obstructionRead diagonal endpoint →
          Cont endpoint cert consumerRead →
            PkgSig bundle consumerRead pkg →
              UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
                UnaryHistory classifier ∧ UnaryHistory route ∧ UnaryHistory obstructionRead ∧
                  UnaryHistory endpoint ∧ UnaryHistory consumerRead ∧
                    Cont classifier route obstructionRead ∧
                      Cont obstructionRead diagonal endpoint ∧
                        Cont endpoint cert consumerRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont UnaryHistory
  intro carrier classifierRouteObstruction obstructionDiagonalEndpoint endpointCertConsumer
    consumerPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, _haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteObstruction
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed obstructionUnary diagonalUnary obstructionDiagonalEndpoint
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary certUnary endpointCertConsumer
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, classifierUnary, routeUnary,
      obstructionUnary, endpointUnary, consumerUnary, classifierRouteObstruction,
      obstructionDiagonalEndpoint, endpointCertConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.HaltingDistinctionUp
