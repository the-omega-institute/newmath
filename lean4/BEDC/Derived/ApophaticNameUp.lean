import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApophaticNameCarrier [AskSetup] [PackageSetup]
    (socket request gate ledger transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
    UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont socket request gate ∧
        Cont request gate route ∧ Cont gate ledger route ∧ Cont gate ledger nameRow ∧
          hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg

theorem ApophaticNameCarrier_refusal_ledger_surface [AskSetup] [PackageSetup]
    {socket request refusal ledger sameRows routes provenance nameCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request refusal ledger sameRows routes provenance nameCert
        bundle pkg ->
      Cont ledger nameCert consumerRead ->
        UnaryHistory consumerRead ∧ UnaryHistory ledger ∧
          hsame ledger (append request refusal) ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerRoute
  obtain ⟨_socketUnary, _requestUnary, _refusalUnary, ledgerUnary, _sameRowsUnary,
    _routesUnary, _provenanceUnary, nameCertUnary, _socketRequestRefusal,
    _requestRefusalRoutes, _refusalLedgerRoutes, _refusalLedgerNameCert, ledgerSameRequestRefusal,
    provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary nameCertUnary consumerRoute
  exact ⟨consumerUnary, ledgerUnary, ledgerSameRequestRefusal, provenancePkg⟩

theorem ApophaticNameCarrier_refusal_ledger [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger route exported ->
        PkgSig bundle exported pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory exported ∧ Cont socket request gate ∧
              Cont gate ledger route ∧ Cont ledger route exported ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg := by
  intro carrier ledgerRouteExported exportedPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteExported
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, exportedUnary, socketRequestGate,
      gateLedgerRoute, ledgerRouteExported, provenancePkg, exportedPkg⟩

end BEDC.Derived.ApophaticNameUp
