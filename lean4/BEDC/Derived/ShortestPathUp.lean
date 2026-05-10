import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ShortestPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ShortestPathVisiblePathLedger [AskSetup] [PackageSetup]
    {vertices edges weights source target incidence path weightLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertices -> UnaryHistory edges -> UnaryHistory weights -> UnaryHistory source ->
      UnaryHistory target -> Cont vertices edges incidence -> Cont incidence weights path ->
        Cont source target weightLedger -> Cont path weightLedger endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory incidence ∧ UnaryHistory path ∧ UnaryHistory weightLedger ∧
              UnaryHistory endpoint ∧ hsame incidence (append vertices edges) ∧
                hsame path (append incidence weights) ∧
                  hsame weightLedger (append source target) ∧
                    hsame endpoint (append path weightLedger) ∧ PkgSig bundle endpoint pkg := by
  intro verticesUnary edgesUnary weightsUnary sourceUnary targetUnary incidenceRow pathRow
    weightLedgerRow endpointRow pkgSig
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed verticesUnary edgesUnary incidenceRow
  have pathUnary : UnaryHistory path :=
    unary_cont_closed incidenceUnary weightsUnary pathRow
  have weightLedgerUnary : UnaryHistory weightLedger :=
    unary_cont_closed sourceUnary targetUnary weightLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed pathUnary weightLedgerUnary endpointRow
  exact
    ⟨incidenceUnary, pathUnary, weightLedgerUnary, endpointUnary, incidenceRow, pathRow,
      weightLedgerRow, endpointRow, pkgSig⟩

end BEDC.Derived.ShortestPathUp
