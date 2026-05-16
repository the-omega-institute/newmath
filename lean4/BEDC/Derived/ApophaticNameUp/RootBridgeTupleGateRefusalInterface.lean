import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_bridge_tuple_gate_refusal_interface [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead refusalRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont gate ledger gateRead ->
        Cont ledger route refusalRead ->
          Cont refusalRead provenance handoffRead ->
            PkgSig bundle handoffRead pkg ->
              UnaryHistory gateRead ∧ UnaryHistory refusalRead ∧ UnaryHistory handoffRead ∧
                Cont socket request gate ∧ Cont gate ledger gateRead ∧
                  Cont ledger route refusalRead ∧ Cont refusalRead provenance handoffRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier gateLedgerRead ledgerRouteRefusal refusalProvenanceHandoff handoffPkg
  obtain ⟨_socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteRefusal
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed refusalReadUnary provenanceUnary refusalProvenanceHandoff
  exact
    ⟨gateReadUnary, refusalReadUnary, handoffReadUnary, socketRequestGate, gateLedgerRead,
      ledgerRouteRefusal, refusalProvenanceHandoff, ledgerSameRequestGate, provenancePkg,
      handoffPkg⟩

theorem ApophaticNameCarrier_root_bridge_tuple_downstream_refusal_uniqueness [AskSetup]
    [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead refusalRead
      handoffRead gateRead' refusalRead' handoffRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont gate ledger gateRead →
        Cont gate ledger gateRead' →
          Cont ledger route refusalRead →
            Cont ledger route refusalRead' →
              Cont refusalRead provenance handoffRead →
                Cont refusalRead' provenance handoffRead' →
                  PkgSig bundle handoffRead pkg →
                    PkgSig bundle handoffRead' pkg →
                      hsame gateRead gateRead' ∧ hsame refusalRead refusalRead' ∧
                        hsame handoffRead handoffRead' ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle handoffRead pkg ∧
                            PkgSig bundle handoffRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier gateReadRoute gateReadRoute' refusalReadRoute refusalReadRoute'
    handoffReadRoute handoffReadRoute' handoffPkg handoffPkg'
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have sameGateRead : hsame gateRead gateRead' :=
    cont_deterministic gateReadRoute gateReadRoute'
  have sameRefusalRead : hsame refusalRead refusalRead' :=
    cont_deterministic refusalReadRoute refusalReadRoute'
  have sameHandoffRead : hsame handoffRead handoffRead' :=
    cont_respects_hsame sameRefusalRead (hsame_refl provenance) handoffReadRoute
      handoffReadRoute'
  exact
    ⟨sameGateRead, sameRefusalRead, sameHandoffRead, provenancePkg, handoffPkg,
      handoffPkg'⟩

end BEDC.Derived.ApophaticNameUp
