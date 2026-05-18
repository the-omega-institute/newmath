import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_socket_provenance [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont gate ledger socketRead ->
        Cont socketRead nameRow boundaryRead ->
          PkgSig bundle boundaryRead pkg ->
            UnaryHistory socketRead ∧ UnaryHistory boundaryRead ∧
              Cont socket request gate ∧ Cont gate ledger socketRead ∧
                Cont socketRead nameRow boundaryRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier socketRoute boundaryRoute boundaryPkg
  obtain ⟨socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed gateUnary ledgerUnary socketRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed socketReadUnary nameRowUnary boundaryRoute
  exact
    ⟨socketReadUnary, boundaryReadUnary, socketRequestGate, socketRoute, boundaryRoute,
      ledgerSameRequestGate, provenancePkg, boundaryPkg⟩

end BEDC.Derived.ApophaticNameUp
