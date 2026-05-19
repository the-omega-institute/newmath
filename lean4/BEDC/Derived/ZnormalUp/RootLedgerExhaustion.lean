import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_ledger_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name ledgerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont routes name ledgerRead →
        PkgSig bundle ledgerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                  hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                    hsame row routes ∨ hsame row ledgerRead)
              (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory ledgerRead ∧ PkgSig bundle name pkg ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet routesNameLedger ledgerPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routesUnary nameUnary routesNameLedger
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                hsame row routes ∨ hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := by
    exact {
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
          intro _row _row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, ledgerPkg⟩
    }
  exact ⟨cert, ledgerUnary, namePkg, provenancePkg, ledgerPkg⟩

end BEDC.Derived.ZnormalUp
