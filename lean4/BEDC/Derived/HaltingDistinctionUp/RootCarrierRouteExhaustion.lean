import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootCarrierRouteExhaustion [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead routeRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont traceRead route routeRead →
          Cont routeRead provenance rootRead →
            PkgSig bundle rootRead pkg →
              UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
                UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory traceRead ∧
                  UnaryHistory routeRead ∧ UnaryHistory rootRead ∧
                    Cont question trace diagonal ∧ Cont trace route traceRead ∧
                      Cont traceRead route routeRead ∧ Cont routeRead provenance rootRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier traceRouteRead traceReadRouteRead routeProvenanceRoot rootPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, provenanceUnary, _certUnary, questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed traceReadUnary routeUnary traceReadRouteRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeReadUnary provenanceUnary routeProvenanceRoot
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, routeUnary, provenanceUnary, traceReadUnary,
      routeReadUnary, rootReadUnary, questionTraceDiagonal, traceRouteRead,
      traceReadRouteRead, routeProvenanceRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.HaltingDistinctionUp
