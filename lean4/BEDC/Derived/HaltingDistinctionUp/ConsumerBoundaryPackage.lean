import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionConsumerBoundaryPackage [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead diagonalRead
      obstructionRead gateRead packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont trace route traceRead ->
        Cont diagonal halt diagonalRead ->
          Cont classifier route obstructionRead ->
            Cont traceRead diagonalRead gateRead ->
              Cont gateRead obstructionRead packageRead ->
                PkgSig bundle packageRead pkg ->
                  UnaryHistory traceRead ∧ UnaryHistory diagonalRead ∧
                    UnaryHistory obstructionRead ∧ UnaryHistory gateRead ∧
                      UnaryHistory packageRead ∧ Cont trace route traceRead ∧
                        Cont diagonal halt diagonalRead ∧
                          Cont classifier route obstructionRead ∧
                            Cont traceRead diagonalRead gateRead ∧
                              Cont gateRead obstructionRead packageRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle packageRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont UnaryHistory
  intro carrier traceRouteRead diagonalHaltRead classifierRouteObstruction
    traceDiagonalGate gateObstructionPackage packagePkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteObstruction
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed traceReadUnary diagonalReadUnary traceDiagonalGate
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed gateReadUnary obstructionReadUnary gateObstructionPackage
  exact
    ⟨traceReadUnary, diagonalReadUnary, obstructionReadUnary, gateReadUnary,
      packageReadUnary, traceRouteRead, diagonalHaltRead, classifierRouteObstruction,
      traceDiagonalGate, gateObstructionPackage, provenancePkg, packagePkg⟩

end BEDC.Derived.HaltingDistinctionUp
