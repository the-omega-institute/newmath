import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HaltingDistinctionCarrier [AskSetup] [PackageSetup]
    (question trace diagonal halt classifier route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧ UnaryHistory halt ∧
    UnaryHistory classifier ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory cert ∧ Cont question trace diagonal ∧ Cont diagonal halt classifier ∧
        Cont classifier route cert ∧ PkgSig bundle provenance pkg

theorem HaltingDistinctionDiagonalBoundary [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert diagonalRead classifierRead
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont diagonal halt diagonalRead ->
        Cont classifier route classifierRead ->
          Cont diagonalRead classifierRead endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory diagonalRead ∧ UnaryHistory classifierRead ∧ UnaryHistory endpoint ∧
                Cont diagonal halt diagonalRead ∧ Cont classifier route classifierRead ∧
                  Cont diagonalRead classifierRead endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalHaltRead classifierRouteRead readEndpoint endpointPkg
  obtain ⟨_questionUnary, _traceUnary, diagonalUnary, haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed diagonalReadUnary classifierReadUnary readEndpoint
  exact
    ⟨diagonalReadUnary, classifierReadUnary, endpointUnary, diagonalHaltRead,
      classifierRouteRead, readEndpoint, provenancePkg, endpointPkg⟩

theorem HaltingDistinctionTraceReadability [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont traceRead classifier endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory traceRead ∧ UnaryHistory endpoint ∧ Cont trace route traceRead ∧
              Cont traceRead classifier endpoint ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier traceRouteRead readClassifierEndpoint endpointPkg
  obtain ⟨_questionUnary, traceUnary, _diagonalUnary, _haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceReadUnary classifierUnary readClassifierEndpoint
  exact
    ⟨traceReadUnary, endpointUnary, traceRouteRead, readClassifierEndpoint, provenancePkg,
      endpointPkg⟩

theorem HaltingDistinctionCarrier_consumer_non_escape [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont classifier route consumerRead →
        PkgSig bundle consumerRead pkg →
          UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
            UnaryHistory halt ∧ UnaryHistory classifier ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory consumerRead ∧
                Cont question trace diagonal ∧ Cont diagonal halt classifier ∧
                  Cont classifier route cert ∧ Cont classifier route consumerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier classifierRouteConsumerRead consumerReadPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
    provenanceUnary, certUnary, questionTraceDiagonal, diagonalHaltClassifier,
    classifierRouteCert, provenancePkg⟩ := carrier
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteConsumerRead
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
      provenanceUnary, certUnary, consumerReadUnary, questionTraceDiagonal,
      diagonalHaltClassifier, classifierRouteCert, classifierRouteConsumerRead, provenancePkg,
      consumerReadPkg⟩

theorem HaltingDistinctionPairClassifierTransport [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert pairRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont question trace pairRead →
        Cont pairRead classifier endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory pairRead ∧ UnaryHistory endpoint ∧ Cont question trace pairRead ∧
              Cont pairRead classifier endpoint ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier questionTracePair pairClassifierEndpoint endpointPkg
  obtain ⟨questionUnary, traceUnary, _diagonalUnary, _haltUnary, classifierUnary,
    _routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have pairUnary : UnaryHistory pairRead :=
    unary_cont_closed questionUnary traceUnary questionTracePair
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed pairUnary classifierUnary pairClassifierEndpoint
  exact
    ⟨pairUnary, endpointUnary, questionTracePair, pairClassifierEndpoint, provenancePkg,
      endpointPkg⟩

theorem HaltingDistinctionFiniteTraceInversion [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont traceRead classifier endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
              UnaryHistory halt ∧ UnaryHistory classifier ∧ UnaryHistory route ∧
                UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory traceRead ∧
                  UnaryHistory endpoint ∧ Cont question trace diagonal ∧
                    Cont diagonal halt classifier ∧ Cont classifier route cert ∧
                      Cont trace route traceRead ∧ Cont traceRead classifier endpoint ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier traceRouteRead readClassifierEndpoint endpointPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary,
    routeUnary, provenanceUnary, certUnary, questionTraceDiagonal, diagonalHaltClassifier,
    classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceReadUnary classifierUnary readClassifierEndpoint
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
      provenanceUnary, certUnary, traceReadUnary, endpointUnary, questionTraceDiagonal,
      diagonalHaltClassifier, classifierRouteCert, traceRouteRead, readClassifierEndpoint,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionUp
