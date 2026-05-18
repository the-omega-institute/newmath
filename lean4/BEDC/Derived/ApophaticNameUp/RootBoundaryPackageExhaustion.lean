import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_boundary_package_exhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow ledgerRead citationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont ledger nameRow ledgerRead ->
        Cont route provenance citationRead ->
          PkgSig bundle ledgerRead pkg ->
            PkgSig bundle citationRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row ledgerRead ∨ hsame row citationRead) ∧
                      ApophaticNameCarrier socket request gate ledger transport route provenance
                        nameRow bundle pkg)
                  (fun row : BHist =>
                    (hsame row ledgerRead ∧ Cont ledger nameRow ledgerRead) ∨
                      (hsame row citationRead ∧ Cont route provenance citationRead))
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧
                      ((hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg) ∨
                        (hsame row citationRead ∧ PkgSig bundle citationRead pkg)))
                  hsame ∧
                UnaryHistory ledgerRead ∧ UnaryHistory citationRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle ledgerRead pkg ∧
                    PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRead routeProvenanceCitation ledgerPkg citationPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have citationReadUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row ledgerRead ∨ hsame row citationRead) ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                bundle pkg)
          (fun row : BHist =>
            (hsame row ledgerRead ∧ Cont ledger nameRow ledgerRead) ∨
              (hsame row citationRead ∧ Cont route provenance citationRead))
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧
              ((hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg) ∨
                (hsame row citationRead ∧ PkgSig bundle citationRead pkg)))
          hsame := by
    exact {
      core := {
        carrier_inhabited := by
          exact Exists.intro ledgerRead
            (And.intro (Or.inl (hsame_refl ledgerRead)) carrierPacket)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          cases source.left with
          | inl sameLedger =>
              exact And.intro
                (Or.inl (hsame_trans (hsame_symm sameRows) sameLedger)) source.right
          | inr sameCitation =>
              exact And.intro
                (Or.inr (hsame_trans (hsame_symm sameRows) sameCitation)) source.right
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameLedger =>
            exact Or.inl (And.intro sameLedger ledgerNameRead)
        | inr sameCitation =>
            exact Or.inr (And.intro sameCitation routeProvenanceCitation)
      ledger_sound := by
        intro _row source
        cases source.left with
        | inl sameLedger =>
            exact And.intro provenancePkg (Or.inl (And.intro sameLedger ledgerPkg))
        | inr sameCitation =>
            exact And.intro provenancePkg (Or.inr (And.intro sameCitation citationPkg))
    }
  exact
    ⟨cert, ledgerReadUnary, citationReadUnary, ledgerSameRequestGate, ledgerPkg,
      citationPkg⟩

end BEDC.Derived.ApophaticNameUp
