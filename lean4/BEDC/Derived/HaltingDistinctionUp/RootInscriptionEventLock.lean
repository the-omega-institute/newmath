import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionCarrier_root_inscription_event_lock [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert diagonalRead traceRead
      eventRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont diagonal halt diagonalRead →
        Cont trace route traceRead →
          Cont diagonalRead traceRead eventRead →
            PkgSig bundle eventRead pkg →
              UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
                UnaryHistory diagonalRead ∧ UnaryHistory traceRead ∧
                  UnaryHistory eventRead ∧ Cont question trace diagonal ∧
                    Cont diagonal halt classifier ∧ Cont diagonal halt diagonalRead ∧
                      Cont trace route traceRead ∧ Cont diagonalRead traceRead eventRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle eventRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalHaltRead traceRouteRead inscriptionEvent eventPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, questionTraceDiagonal,
    diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have eventReadUnary : UnaryHistory eventRead :=
    unary_cont_closed diagonalReadUnary traceReadUnary inscriptionEvent
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, diagonalReadUnary, traceReadUnary,
      eventReadUnary, questionTraceDiagonal, diagonalHaltClassifier, diagonalHaltRead,
      traceRouteRead, inscriptionEvent, provenancePkg, eventPkg⟩

end BEDC.Derived.HaltingDistinctionUp
