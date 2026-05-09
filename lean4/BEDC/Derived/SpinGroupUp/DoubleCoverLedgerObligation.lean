import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.CliffordUp
open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_double_cover_ledger_obligation [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger
      coverEndpoint coverLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont spinEndpoint BHist.Empty coverEndpoint ->
        Cont coverEndpoint groupWord coverLedger ->
          UnaryHistory coverEndpoint ∧ UnaryHistory coverLedger ∧
            hsame coverEndpoint spinEndpoint ∧
              hsame coverLedger (append coverEndpoint groupWord) ∧
                CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
                  GroupSingletonCarrier groupWord ∧
                    Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier coverEndpointRow coverLedgerRow
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm sourceScope.right.left)
  have coverEndpointUnary : UnaryHistory coverEndpoint :=
    unary_cont_closed sourceScope.right.right.left unary_empty coverEndpointRow
  have coverLedgerUnary : UnaryHistory coverLedger :=
    unary_cont_closed coverEndpointUnary groupUnary coverLedgerRow
  exact
    ⟨coverEndpointUnary, coverLedgerUnary, cont_right_unit_result coverEndpointRow,
      coverLedgerRow, sourceScope.left, sourceScope.right.left,
      sourceScope.right.right.right.left, sourceScope.right.right.right.right⟩

end BEDC.Derived.SpinGroupUp
