import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_public_finite_window_export [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      Cont ledger provenance publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont ledger provenance row ∧ PkgSig bundle row pkg)
            (fun row : BHist =>
              DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ∧
                UnaryHistory row)
            hsame := by
  intro carrier ledgerProvenancePublic publicPkg
  have carrierData :
      DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg :=
    carrier
  obtain ⟨_precisionUnary, _endpointUnary, _windowUnary, ledgerUnary, provenanceUnary,
    _precisionEndpointWindow, _windowLedgerProvenance, _provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenancePublic
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary, publicPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨ledgerProvenancePublic, publicPkg⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨carrierData, sourceRow.right.left⟩
  }

end BEDC.Derived.DyadicApproximationUp
