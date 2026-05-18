import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameSocketBoundaryRouteExhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow boundaryRead exported :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont socket request boundaryRead ->
        Cont boundaryRead gate exported ->
          PkgSig bundle exported pkg ->
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory boundaryRead ∧ UnaryHistory exported ∧
                Cont socket request boundaryRead ∧ Cont boundaryRead gate exported ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier socketRequestBoundary boundaryGateExported exportedPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed socketUnary requestUnary socketRequestBoundary
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed boundaryReadUnary gateUnary boundaryGateExported
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, boundaryReadUnary, exportedUnary,
      socketRequestBoundary, boundaryGateExported, provenancePkg, exportedPkg⟩

end BEDC.Derived.ApophaticNameUp
