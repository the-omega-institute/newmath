import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_boundary_ledger_package [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citationRead requestRead
      gateRead ledgerRead packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont route provenance citationRead ->
        Cont request gate requestRead ->
          Cont gate ledger gateRead ->
            Cont ledger nameRow ledgerRead ->
              Cont ledgerRead provenance packageRead ->
                PkgSig bundle citationRead pkg ->
                  PkgSig bundle requestRead pkg ->
                    PkgSig bundle packageRead pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            ApophaticNameCarrier socket request gate ledger transport route
                              provenance nameRow bundle pkg ∧ hsame row request)
                          (fun row : BHist =>
                            hsame row request ∧ UnaryHistory row ∧
                              Cont request gate requestRead)
                          (fun row : BHist =>
                            PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg ∧
                              hsame row request ∧ Cont request gate requestRead)
                          hsame ∧
                        SemanticNameCert
                            (fun row : BHist =>
                              ApophaticNameCarrier socket request gate ledger transport route
                                provenance nameRow bundle pkg ∧ hsame row gate)
                            (fun row : BHist =>
                              hsame row gate ∧ UnaryHistory row ∧
                                Cont request gate requestRead)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle packageRead pkg ∧
                                hsame row gate ∧ Cont ledgerRead provenance packageRead)
                            hsame ∧
                          UnaryHistory citationRead ∧ UnaryHistory requestRead ∧
                            UnaryHistory gateRead ∧ UnaryHistory ledgerRead ∧
                              UnaryHistory packageRead ∧ hsame ledger (append request gate) ∧
                                PkgSig bundle citationRead pkg ∧
                                  PkgSig bundle requestRead pkg ∧
                                    PkgSig bundle packageRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceCitation requestGateRead gateLedgerRead ledgerNameRead
    ledgerReadProvenancePackage citationPkg requestReadPkg packagePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
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
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed ledgerReadUnary provenanceUnary ledgerReadProvenancePackage
  have requestCert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row request)
          (fun row : BHist =>
            hsame row request ∧ UnaryHistory row ∧ Cont request gate requestRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg ∧
              hsame row request ∧ Cont request gate requestRead)
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
            requestGateRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, requestReadPkg, source.right, requestGateRead⟩
    }
  have gateCert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row gate)
          (fun row : BHist =>
            hsame row gate ∧ UnaryHistory row ∧ Cont request gate requestRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle packageRead pkg ∧
              hsame row gate ∧ Cont ledgerRead provenance packageRead)
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
        exact ⟨provenancePkg, packagePkg, source.right, ledgerReadProvenancePackage⟩
    }
  exact
    ⟨requestCert, gateCert, citationReadUnary, requestReadUnary, gateReadUnary,
      ledgerReadUnary, packageReadUnary, ledgerSameRequestGate, citationPkg, requestReadPkg,
      packagePkg⟩

end BEDC.Derived.ApophaticNameUp
