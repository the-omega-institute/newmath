import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionInscriptionTraceGate [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead diagonalRead
      gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont diagonal halt diagonalRead →
          Cont traceRead diagonalRead gateRead →
            PkgSig bundle gateRead pkg →
              UnaryHistory traceRead ∧ UnaryHistory diagonalRead ∧ UnaryHistory gateRead ∧
                Cont trace route traceRead ∧ Cont diagonal halt diagonalRead ∧
                  Cont traceRead diagonalRead gateRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle gateRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier traceRouteRead diagonalHaltRead readGate gatePkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed traceReadUnary diagonalReadUnary readGate
  exact
    ⟨traceReadUnary, diagonalReadUnary, gateReadUnary, traceRouteRead, diagonalHaltRead,
      readGate, provenancePkg, gatePkg⟩

end BEDC.Derived.HaltingDistinctionUp
