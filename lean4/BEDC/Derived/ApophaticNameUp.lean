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
    UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory nameRow ∧
      Cont socket request gate ∧ Cont gate ledger route ∧ PkgSig bundle provenance pkg

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
    _nameRowUnary, socketRequestGate, gateLedgerRoute, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteExported
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, exportedUnary, socketRequestGate,
      gateLedgerRoute, ledgerRouteExported, provenancePkg, exportedPkg⟩

end BEDC.Derived.ApophaticNameUp
