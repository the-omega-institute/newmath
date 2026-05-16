import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_gate_ledger_pullback [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead gateRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont request gate socketRead →
        Cont gate ledger gateRead →
          Cont ledger nameRow ledgerRead →
            PkgSig bundle socketRead pkg →
              PkgSig bundle gateRead pkg →
                PkgSig bundle ledgerRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        ApophaticNameCarrier socket request gate ledger transport route
                          provenance nameRow bundle pkg ∧ hsame row request)
                      (fun row : BHist =>
                        hsame row request ∧ UnaryHistory row ∧ Cont request gate socketRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle socketRead pkg ∧
                          hsame row request ∧ Cont request gate socketRead)
                      hsame ∧
                    SemanticNameCert
                        (fun row : BHist =>
                          ApophaticNameCarrier socket request gate ledger transport route
                            provenance nameRow bundle pkg ∧ hsame row ledger)
                        (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
                        (fun row : BHist =>
                          PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                            hsame row (append request gate) ∧
                              Cont ledger nameRow ledgerRead)
                        hsame ∧
                      UnaryHistory socketRead ∧ UnaryHistory gateRead ∧
                        UnaryHistory ledgerRead ∧ Cont request gate socketRead ∧
                          Cont gate ledger gateRead ∧ Cont ledger nameRow ledgerRead ∧
                            hsame ledger (append request gate) ∧
                              PkgSig bundle socketRead pkg ∧ PkgSig bundle gateRead pkg ∧
                                PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateSocket gateLedgerRead ledgerNameRead socketPkg gatePkg ledgerPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed requestUnary gateUnary requestGateSocket
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have requestCert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row request)
          (fun row : BHist =>
            hsame row request ∧ UnaryHistory row ∧ Cont request gate socketRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle socketRead pkg ∧
              hsame row request ∧ Cont request gate socketRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro request ⟨carrierPacket, hsame_refl request⟩
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
          ⟨source.right, unary_transport requestUnary (hsame_symm source.right),
            requestGateSocket⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, socketPkg, source.right, requestGateSocket⟩
    }
  have ledgerCert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledger)
          (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
              hsame row (append request gate) ∧ Cont ledger nameRow ledgerRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
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
        have rowSameLedger : hsame _row ledger := source.right
        exact
          ⟨hsame_trans rowSameLedger ledgerSameRequestGate,
            unary_transport ledgerUnary (hsame_symm rowSameLedger)⟩
      ledger_sound := by
        intro _row source
        have rowSameLedger : hsame _row ledger := source.right
        exact
          ⟨provenancePkg, ledgerPkg, hsame_trans rowSameLedger ledgerSameRequestGate,
            ledgerNameRead⟩
    }
  exact
    ⟨requestCert, ledgerCert, socketReadUnary, gateReadUnary, ledgerReadUnary,
      requestGateSocket, gateLedgerRead, ledgerNameRead, ledgerSameRequestGate,
      socketPkg, gatePkg, ledgerPkg⟩

end BEDC.Derived.ApophaticNameUp
