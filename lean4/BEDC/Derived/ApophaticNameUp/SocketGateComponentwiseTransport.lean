import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_gate_componentwise_transport [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont socket request socketRead ->
        Cont gate ledger gateRead ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row transport)
                (fun row : BHist => hsame row transport ∧ Cont socket request socketRead)
                (fun _row : BHist => PkgSig bundle provenance pkg ∧ Cont gate ledger gateRead)
                hsame ∧
              UnaryHistory socketRead ∧ UnaryHistory gateRead ∧
                hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestRead gateLedgerRead provenancePkg'
  obtain
    ⟨socketUnary, requestUnary, _gateUnary, ledgerUnary, transportUnary, _routeUnary,
      _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩ :=
    carrier
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    ⟨socketUnary, requestUnary, _gateUnary, ledgerUnary, transportUnary, _routeUnary,
      _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg'⟩
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRead
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed _gateUnary ledgerUnary gateLedgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row transport)
          (fun row : BHist => hsame row transport ∧ Cont socket request socketRead)
          (fun _row : BHist => PkgSig bundle provenance pkg ∧ Cont gate ledger gateRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro transport ⟨carrierPacket, hsame_refl transport⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, socketRequestRead⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg', gateLedgerRead⟩
    }
  exact ⟨cert, socketReadUnary, gateReadUnary, ledgerSameRequestGate⟩

end BEDC.Derived.ApophaticNameUp
