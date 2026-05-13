import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_real_seal_scope [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance sealRow consumer sealSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      Cont ledger provenance sealRow ->
        Cont window provenance consumer ->
          Cont sealRow consumer sealSurface ->
            PkgSig bundle sealRow pkg ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle sealSurface pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      (hsame row sealRow ∨ hsame row consumer ∨ hsame row sealSurface) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      Cont ledger provenance row ∨ Cont window provenance row ∨
                        Cont sealRow consumer row)
                    (fun row : BHist =>
                      PkgSig bundle row pkg ∧ UnaryHistory precision ∧ UnaryHistory endpoint ∧
                        UnaryHistory window ∧ UnaryHistory ledger ∧ UnaryHistory provenance)
                    (fun row row' : BHist => hsame row row') := by
  intro carrier ledgerProvenanceSeal windowProvenanceConsumer sealConsumerSurface
    sealPkg consumerPkg surfacePkg
  obtain ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
    _precisionEndpointWindow, _windowLedgerProvenance, _provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary provenanceUnary windowProvenanceConsumer
  have surfaceUnary : UnaryHistory sealSurface :=
    unary_cont_closed sealUnary consumerUnary sealConsumerSurface
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow (And.intro (Or.inl (hsame_refl sealRow)) sealUnary)
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
      intro row sourceRow
      cases sourceRow.left with
      | inl sameSeal =>
          cases sameSeal
          exact Or.inl ledgerProvenanceSeal
      | inr remaining =>
          cases remaining with
          | inl sameConsumer =>
              cases sameConsumer
              exact Or.inr (Or.inl windowProvenanceConsumer)
          | inr sameSurface =>
              cases sameSurface
              exact Or.inr (Or.inr sealConsumerSurface)
    ledger_sound := by
      intro row sourceRow
      cases sourceRow.left with
      | inl sameSeal =>
          cases sameSeal
          exact
            ⟨sealPkg, precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary⟩
      | inr remaining =>
          cases remaining with
          | inl sameConsumer =>
              cases sameConsumer
              exact
                ⟨consumerPkg, precisionUnary, endpointUnary, windowUnary, ledgerUnary,
                  provenanceUnary⟩
          | inr sameSurface =>
              cases sameSurface
              exact
                ⟨surfacePkg, precisionUnary, endpointUnary, windowUnary, ledgerUnary,
                  provenanceUnary⟩
  }

end BEDC.Derived.DyadicApproximationUp
