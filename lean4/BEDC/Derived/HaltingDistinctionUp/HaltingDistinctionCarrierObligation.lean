import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert exposure : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont question route exposure ->
        PkgSig bundle exposure pkg ->
          UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
            UnaryHistory halt ∧ UnaryHistory classifier ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory exposure ∧
                Cont question trace diagonal ∧ Cont diagonal halt classifier ∧
                  Cont classifier route cert ∧ Cont question route exposure ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle exposure pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier questionRouteExposure exposurePkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
    provenanceUnary, certUnary, questionTraceDiagonal, diagonalHaltClassifier,
    classifierRouteCert, provenancePkg⟩ := carrier
  have exposureUnary : UnaryHistory exposure :=
    unary_cont_closed questionUnary routeUnary questionRouteExposure
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
      provenanceUnary, certUnary, exposureUnary, questionTraceDiagonal, diagonalHaltClassifier,
      classifierRouteCert, questionRouteExposure, provenancePkg, exposurePkg⟩

end BEDC.Derived.HaltingDistinctionUp
