import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_normal_form_ledger_row [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont terminal normal ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row terminal ∨ hsame row normal ∨ hsame row ledgerRead ∨
                  hsame row transports ∨ hsame row routes)
              (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory terminal ∧ UnaryHistory normal ∧ UnaryHistory ledgerRead ∧
              Cont terminal normal ledgerRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalNormalLedger ledgerPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuel,
    _terminalNormalContinuation, _continuationTransports, _namePkg, provenancePkg⟩ := packet
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalLedger
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row terminal ∨ hsame row normal ∨ hsame row ledgerRead ∨
            hsame row transports ∨ hsame row routes)
        (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact Or.inr (Or.inr (Or.inl (hsame_refl ledgerRead)))
    ledger_sound := by
      intro row source
      exact ⟨source.left, ledgerPkg⟩
  }
  exact
    ⟨cert, terminalUnary, normalUnary, ledgerUnary, terminalNormalLedger, provenancePkg,
      ledgerPkg⟩

end BEDC.Derived.ZnormalUp
