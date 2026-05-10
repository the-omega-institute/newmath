import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ShortestPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ShortestPathBHistWeightedGraphCarrier [AskSetup] [PackageSetup]
    (vertices edges weights source target path incidenceLedger weightLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vertices ∧ UnaryHistory edges ∧ UnaryHistory weights ∧
    UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory path ∧
      Cont vertices edges incidenceLedger ∧ Cont weights path weightLedger ∧
        Cont incidenceLedger weightLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem ShortestPathBHistWeightedGraphCarrier_visible_path_ledger [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidenceLedger weightLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathBHistWeightedGraphCarrier vertices edges weights source target path
        incidenceLedger weightLedger endpoint bundle pkg ->
      UnaryHistory vertices ∧ UnaryHistory edges ∧ UnaryHistory weights ∧
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory path ∧
          UnaryHistory incidenceLedger ∧ UnaryHistory weightLedger ∧
            UnaryHistory endpoint ∧ hsame incidenceLedger (append vertices edges) ∧
              hsame weightLedger (append weights path) ∧
                hsame endpoint (append incidenceLedger weightLedger) ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier
  have incidenceLedgerUnary : UnaryHistory incidenceLedger :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have weightLedgerUnary : UnaryHistory weightLedger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed incidenceLedgerUnary weightLedgerUnary
      carrier.right.right.right.right.right.right.right.right.left
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left, incidenceLedgerUnary, weightLedgerUnary,
      endpointUnary, carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.ShortestPathUp
