import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootCarrierSurface [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont question trace diagonal →
        Cont trace route endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
              UnaryHistory halt ∧ UnaryHistory classifier ∧ UnaryHistory route ∧
                UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
                  Cont question trace diagonal ∧ Cont trace route endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier questionTraceDiagonal traceRouteEndpoint endpointPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
    provenanceUnary, certUnary, _carrierQuestionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceUnary routeUnary traceRouteEndpoint
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
      provenanceUnary, certUnary, endpointUnary, questionTraceDiagonal, traceRouteEndpoint,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionUp
