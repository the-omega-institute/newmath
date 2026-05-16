import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_refusal_gate_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow refusalRead →
        PkgSig bundle refusalRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row gate)
              (fun row : BHist => hsame row gate ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ hsame row gate ∧
                  Cont socket request gate ∧ Cont gate ledger nameRow)
              hsame ∧
            UnaryHistory gate ∧ UnaryHistory ledger ∧ Cont socket request gate ∧
              Cont gate ledger nameRow ∧ Cont ledger nameRow refusalRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRefusal refusalPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row gate)
          (fun row : BHist => hsame row gate ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row gate ∧
              Cont socket request gate ∧ Cont gate ledger nameRow)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gate ⟨carrierPacket, hsame_refl gate⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameGate : hsame row gate := source.right
      exact ⟨rowSameGate, unary_transport gateUnary (hsame_symm rowSameGate)⟩
    · intro row source
      exact ⟨provenancePkg, source.right, socketRequestGate, gateLedgerNameRow⟩
  exact
    ⟨cert, gateUnary, ledgerUnary, socketRequestGate, gateLedgerNameRow,
      ledgerNameRefusal, provenancePkg, refusalPkg⟩

theorem ApophaticNameCarrier_refusal_gate_ledger_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont gate ledger gateRead →
        Cont ledger nameRow ledgerRead →
          PkgSig bundle gateRead pkg →
            PkgSig bundle ledgerRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row gate)
                  (fun row : BHist =>
                    hsame row gate ∧ UnaryHistory row ∧ Cont gate ledger gateRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                      hsame row gate ∧ Cont ledger nameRow ledgerRead)
                  hsame ∧
                UnaryHistory gateRead ∧ UnaryHistory ledgerRead ∧
                  hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gateLedgerRead ledgerNameRead _gatePkg ledgerPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row gate)
          (fun row : BHist =>
            hsame row gate ∧ UnaryHistory row ∧ Cont gate ledger gateRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
              hsame row gate ∧ Cont ledger nameRow ledgerRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro gate ⟨carrierPacket, hsame_refl gate⟩
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
        exact
          ⟨source.right, unary_transport gateUnary (hsame_symm source.right),
            gateLedgerRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, ledgerPkg, source.right, ledgerNameRead⟩
    }
  exact ⟨cert, gateReadUnary, ledgerReadUnary, ledgerSameRequestGate⟩

end BEDC.Derived.ApophaticNameUp
