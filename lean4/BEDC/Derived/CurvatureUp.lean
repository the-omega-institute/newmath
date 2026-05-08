import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureBracketCarrier_visible_ledger_coverage [AskSetup] [PackageSetup]
    {connection base fibre secRow tangentLeft tangentRight derivativeLeftRight
      derivativeRightLeft boundary ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory connection ->
      UnaryHistory base ->
        UnaryHistory fibre ->
          UnaryHistory secRow ->
            UnaryHistory tangentLeft ->
              UnaryHistory tangentRight ->
                UnaryHistory derivativeLeftRight ->
                  UnaryHistory derivativeRightLeft ->
                    UnaryHistory ledger ->
                      Cont derivativeLeftRight derivativeRightLeft boundary ->
                        Cont boundary ledger endpoint ->
                          PkgSig bundle endpoint pkg ->
                            UnaryHistory boundary ∧
                              UnaryHistory endpoint ∧
                                hsame boundary
                                  (append derivativeLeftRight derivativeRightLeft) ∧
                                  hsame endpoint
                                    (append (append derivativeLeftRight derivativeRightLeft)
                                      ledger) ∧
                                    PkgSig bundle endpoint pkg := by
  intro _connectionUnary _baseUnary _fibreUnary _secUnary _tangentLeftUnary
    _tangentRightUnary derivativeLeftRightUnary derivativeRightLeftUnary ledgerUnary
    boundaryCont endpointCont pkgSig
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed derivativeLeftRightUnary derivativeRightLeftUnary boundaryCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed boundaryUnary ledgerUnary endpointCont
  have endpointReadback :
      hsame endpoint (append (append derivativeLeftRight derivativeRightLeft) ledger) :=
    endpointCont.trans
      (congrArg (fun row : BHist => append row ledger) boundaryCont)
  exact And.intro boundaryUnary
    (And.intro endpointUnary
      (And.intro boundaryCont
        (And.intro endpointReadback pkgSig)))

end BEDC.Derived.CurvatureUp
