import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_refusal_gate_readback [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestRead gateRead
      ledgerRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont request gate requestRead ->
        Cont gate ledger gateRead ->
          Cont ledger nameRow ledgerRead ->
            Cont ledgerRead provenance rootRead ->
              PkgSig bundle rootRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      ApophaticNameCarrier socket request gate ledger transport route
                        provenance nameRow bundle pkg ∧ hsame row gate)
                    (fun row : BHist =>
                      hsame row gate ∧ UnaryHistory row ∧ Cont request gate requestRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                        hsame row gate ∧ Cont ledgerRead provenance rootRead)
                    hsame ∧
                  UnaryHistory requestRead ∧ UnaryHistory gateRead ∧
                    UnaryHistory ledgerRead ∧ UnaryHistory rootRead ∧
                      Cont request gate requestRead ∧ Cont gate ledger gateRead ∧
                        Cont ledger nameRow ledgerRead ∧ Cont ledgerRead provenance rootRead ∧
                          hsame ledger (append request gate) ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateRead gateLedgerRead ledgerNameRead ledgerReadProvenanceRoot rootPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerReadUnary provenanceUnary ledgerReadProvenanceRoot
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row gate)
          (fun row : BHist =>
            hsame row gate ∧ UnaryHistory row ∧ Cont request gate requestRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              hsame row gate ∧ Cont ledgerRead provenance rootRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro gate ⟨carrierPacket, hsame_refl gate⟩
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
            requestGateRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, rootPkg, source.right, ledgerReadProvenanceRoot⟩
    }
  exact
    ⟨cert, requestReadUnary, gateReadUnary, ledgerReadUnary, rootReadUnary,
      requestGateRead, gateLedgerRead, ledgerNameRead, ledgerReadProvenanceRoot,
      ledgerSameRequestGate, rootPkg⟩

theorem ApophaticNameCarrier_root_citation_readback_package [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citationRead requestRead
      gateRead ledgerRead rootRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont route provenance citationRead →
        PkgSig bundle citationRead pkg →
          Cont request gate requestRead →
            Cont gate ledger gateRead →
              Cont ledger nameRow ledgerRead →
                Cont ledgerRead provenance rootRead →
                  PkgSig bundle rootRead pkg →
                    Cont ledger nameRow boundaryRead →
                      PkgSig bundle boundaryRead pkg →
                        UnaryHistory citationRead ∧ UnaryHistory requestRead ∧
                          UnaryHistory gateRead ∧ UnaryHistory ledgerRead ∧
                            UnaryHistory rootRead ∧ UnaryHistory boundaryRead ∧
                              Cont request gate requestRead ∧ Cont gate ledger gateRead ∧
                                Cont ledger nameRow ledgerRead ∧
                                  Cont ledgerRead provenance rootRead ∧
                                    Cont ledger nameRow boundaryRead ∧
                                      hsame ledger (append request gate) ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle citationRead pkg ∧
                                            PkgSig bundle rootRead pkg ∧
                                              PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier routeProvenanceCitation citationPkg requestGateRead gateLedgerRead
    ledgerNameRead ledgerReadProvenanceRoot rootPkg ledgerNameBoundary boundaryPkg
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have citationReadUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerReadUnary provenanceUnary ledgerReadProvenanceRoot
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameBoundary
  exact
    ⟨citationReadUnary, requestReadUnary, gateReadUnary, ledgerReadUnary, rootReadUnary,
      boundaryReadUnary, requestGateRead, gateLedgerRead, ledgerNameRead,
      ledgerReadProvenanceRoot, ledgerNameBoundary, ledgerSameRequestGate, provenancePkg,
      citationPkg, rootPkg, boundaryPkg⟩

end BEDC.Derived.ApophaticNameUp
