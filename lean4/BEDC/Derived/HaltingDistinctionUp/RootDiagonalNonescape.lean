import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootDiagonalNonescape [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert diagonalRead classifierRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont diagonal halt diagonalRead →
        Cont classifier route classifierRead →
          Cont diagonalRead classifierRead rootRead →
            PkgSig bundle rootRead pkg →
              UnaryHistory question ∧ UnaryHistory trace ∧ UnaryHistory diagonal ∧
                UnaryHistory halt ∧ UnaryHistory classifier ∧ UnaryHistory route ∧
                  UnaryHistory diagonalRead ∧ UnaryHistory classifierRead ∧
                    UnaryHistory rootRead ∧ Cont question trace diagonal ∧
                      Cont diagonal halt diagonalRead ∧ Cont classifier route classifierRead ∧
                        Cont diagonalRead classifierRead rootRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalHaltRead classifierRouteRead diagonalClassifierRoot rootPkg
  obtain ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed diagonalReadUnary classifierReadUnary diagonalClassifierRoot
  exact
    ⟨questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary, routeUnary,
      diagonalReadUnary, classifierReadUnary, rootReadUnary, questionTraceDiagonal,
      diagonalHaltRead, classifierRouteRead, diagonalClassifierRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.HaltingDistinctionUp
