import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRouteObstructionTriad [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead diagonalRead
      obstructionRead triadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont diagonal halt diagonalRead →
          Cont classifier route obstructionRead →
            Cont traceRead obstructionRead triadRead →
              PkgSig bundle triadRead pkg →
                UnaryHistory traceRead ∧ UnaryHistory diagonalRead ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory triadRead ∧
                    Cont trace route traceRead ∧ Cont diagonal halt diagonalRead ∧
                      Cont classifier route obstructionRead ∧
                        Cont traceRead obstructionRead triadRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle triadRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier traceRouteRead diagonalHaltRead classifierRouteObstruction
    traceObstructionTriad triadPkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
    _provenanceUnary, _certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteObstruction
  have triadReadUnary : UnaryHistory triadRead :=
    unary_cont_closed traceReadUnary obstructionReadUnary traceObstructionTriad
  exact
    ⟨traceReadUnary, diagonalReadUnary, obstructionReadUnary, triadReadUnary,
      traceRouteRead, diagonalHaltRead, classifierRouteObstruction, traceObstructionTriad,
      provenancePkg, triadPkg⟩

end BEDC.Derived.HaltingDistinctionUp
