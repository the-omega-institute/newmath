import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_export_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow exportRead ->
        PkgSig bundle exportRead pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory nameRow ∧ UnaryHistory exportRead ∧
              Cont socket request gate ∧ Cont request gate route ∧
                Cont gate ledger route ∧ Cont ledger nameRow exportRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier exportRoute exportPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute,
    gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed ledgerUnary nameRowUnary exportRoute
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, nameRowUnary, exportUnary,
      socketRequestGate, requestGateRoute, gateLedgerRoute, exportRoute,
      ledgerSameRequestGate, provenancePkg, exportPkg⟩

end BEDC.Derived.ApophaticNameUp
