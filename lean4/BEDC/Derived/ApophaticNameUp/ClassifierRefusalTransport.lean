import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_classifier_refusal_transport [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont gate ledger classifierRead ->
        PkgSig bundle classifierRead pkg ->
          UnaryHistory classifierRead ∧ hsame ledger (append request gate) ∧
            Cont socket request gate ∧ Cont gate ledger classifierRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier gateLedgerClassifier classifierPkg
  obtain ⟨_socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerClassifier
  exact
    ⟨classifierUnary, ledgerSameRequestGate, socketRequestGate, gateLedgerClassifier,
      provenancePkg, classifierPkg⟩

end BEDC.Derived.ApophaticNameUp
