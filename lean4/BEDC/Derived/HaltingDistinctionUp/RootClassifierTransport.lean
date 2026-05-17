import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootClassifierTransport [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead publicRead
      diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont question trace traceRead ->
        Cont traceRead classifier publicRead ->
          Cont diagonal halt diagonalRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory traceRead ∧ UnaryHistory publicRead ∧
                UnaryHistory diagonalRead ∧ Cont question trace traceRead ∧
                  Cont traceRead classifier publicRead ∧ Cont diagonal halt diagonalRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier questionTraceRead traceReadClassifierPublic diagonalHaltRead publicPkg
  obtain
    ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, _routeUnary,
      _provenanceUnary, _certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
      _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed questionUnary traceUnary questionTraceRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed traceReadUnary classifierUnary traceReadClassifierPublic
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  exact
    ⟨traceReadUnary, publicReadUnary, diagonalReadUnary, questionTraceRead,
      traceReadClassifierPublic, diagonalHaltRead, provenancePkg, publicPkg⟩

end BEDC.Derived.HaltingDistinctionUp
