import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_public_ledger_package_export [AskSetup] [PackageSetup]
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

theorem DyadicApproximationCarrier_public_finite_window_export [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance consumer sealRow localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      Cont window provenance consumer ->
        Cont ledger provenance sealRow ->
          PkgSig bundle consumer pkg ->
            PkgSig bundle sealRow pkg ->
              PkgSig bundle localName pkg ->
                SemanticNameCert
                  (fun row : BHist => (hsame row consumer \/ hsame row sealRow) ∧
                    UnaryHistory row)
                  (fun row : BHist => Cont window provenance row \/
                    Cont ledger provenance row)
                  (fun row : BHist =>
                    PkgSig bundle row pkg ∧ PkgSig bundle localName pkg ∧
                      UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
                        UnaryHistory ledger ∧ UnaryHistory provenance)
                  (fun row row' : BHist => hsame row row') := by
  intro carrier windowProvenanceConsumer ledgerProvenanceSeal consumerPkg sealPkg localPkg
  obtain ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
    _precisionEndpointWindow, _windowLedgerProvenance, _provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary provenanceUnary windowProvenanceConsumer
  have sourceConsumer :
      (hsame consumer consumer \/ hsame consumer sealRow) ∧ UnaryHistory consumer :=
    ⟨Or.inl (hsame_refl consumer), consumerUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer sourceConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left with
      | inl sameConsumer =>
          cases sameConsumer
          exact Or.inl windowProvenanceConsumer
      | inr sameSeal =>
          cases sameSeal
          exact Or.inr ledgerProvenanceSeal
    ledger_sound := by
      intro row source
      cases source.left with
      | inl sameConsumer =>
          cases sameConsumer
          exact
            ⟨consumerPkg, localPkg, precisionUnary, endpointUnary, windowUnary, ledgerUnary,
              provenanceUnary⟩
      | inr sameSeal =>
          cases sameSeal
          exact
            ⟨sealPkg, localPkg, precisionUnary, endpointUnary, windowUnary, ledgerUnary,
              provenanceUnary⟩
  }

end BEDC.Derived.DyadicApproximationUp
