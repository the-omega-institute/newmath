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
    (socket request refusal ledger sameRows routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory refusal ∧
    UnaryHistory ledger ∧ UnaryHistory sameRows ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont socket request sameRows ∧
        Cont request refusal routes ∧ Cont refusal ledger nameCert ∧
          hsame ledger (append request refusal) ∧ PkgSig bundle provenance pkg

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
    _routesUnary, _provenanceUnary, nameCertUnary, _socketRequestRoute,
    _requestRefusalRoute, _refusalLedgerRoute, ledgerSameRequestRefusal,
    provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary nameCertUnary consumerRoute
  exact ⟨consumerUnary, ledgerUnary, ledgerSameRequestRefusal, provenancePkg⟩

end BEDC.Derived.ApophaticNameUp
