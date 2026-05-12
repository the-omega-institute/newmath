import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_seal_common_refinement_pullback
    [AskSetup] [PackageSetup]
    {precisionA endpointA windowA ledgerA provenanceA precisionB endpointB windowB ledgerB
      provenanceB commonPrecision commonEndpoint commonWindow commonLedger commonProvenance
      sealRow meshCell enclosure : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precisionA endpointA windowA ledgerA provenanceA bundle pkg ->
      DyadicApproximationCarrier precisionB endpointB windowB ledgerB provenanceB bundle pkg ->
        hsame precisionA commonPrecision ->
          hsame precisionB commonPrecision ->
            hsame endpointA commonEndpoint ->
              hsame endpointB commonEndpoint ->
                hsame ledgerA commonLedger ->
                  hsame ledgerB commonLedger ->
                    hsame provenanceA commonProvenance ->
                      hsame provenanceB commonProvenance ->
                        Cont commonPrecision commonEndpoint commonWindow ->
                          Cont commonWindow commonLedger commonProvenance ->
                            Cont commonLedger commonProvenance sealRow ->
                              Cont commonWindow commonProvenance meshCell ->
                                Cont meshCell commonProvenance enclosure ->
                                  PkgSig bundle sealRow pkg ->
                                    PkgSig bundle meshCell pkg ->
                                      PkgSig bundle enclosure pkg ->
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            DyadicApproximationCarrier commonPrecision
                                              commonEndpoint commonWindow commonLedger
                                              commonProvenance bundle pkg ∧
                                                (hsame row sealRow ∨ hsame row meshCell ∨
                                                  hsame row enclosure) ∧
                                                  UnaryHistory row)
                                          (fun row : BHist =>
                                            Cont commonLedger commonProvenance sealRow ∧
                                              Cont commonWindow commonProvenance meshCell ∧
                                                Cont meshCell commonProvenance enclosure ∧
                                                  UnaryHistory row)
                                          (fun _row : BHist =>
                                            PkgSig bundle sealRow pkg ∧
                                              PkgSig bundle meshCell pkg ∧
                                                PkgSig bundle enclosure pkg)
                                          hsame := by
  intro carrierA carrierB samePrecisionA samePrecisionB sameEndpointA sameEndpointB
  intro sameLedgerA sameLedgerB sameProvenanceA sameProvenanceB
  intro commonPrecisionEndpointWindow commonWindowLedgerProvenance
  intro commonLedgerProvenanceSeal commonWindowProvenanceMesh meshProvenanceEnclosure
  intro sealPkg meshPkg enclosurePkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame windowA commonWindow ∧ hsame windowB commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrierA carrierB
      samePrecisionA samePrecisionB sameEndpointA sameEndpointB sameLedgerA sameLedgerB
      sameProvenanceA sameProvenanceB commonPrecisionEndpointWindow
      commonWindowLedgerProvenance
  obtain ⟨_commonPrecisionUnary, _commonEndpointUnary, commonWindowUnary,
    commonLedgerUnary, commonProvenanceUnary, _commonPrecisionEndpointWindow,
    _commonWindowLedgerProvenance, _commonPkg⟩ := refined.left
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed commonLedgerUnary commonProvenanceUnary commonLedgerProvenanceSeal
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceMesh
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed meshUnary commonProvenanceUnary meshProvenanceEnclosure
  have sourceSeal :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        (hsame sealRow sealRow ∨ hsame sealRow meshCell ∨ hsame sealRow enclosure) ∧
          UnaryHistory sealRow :=
    ⟨refined.left, Or.inl (hsame_refl sealRow), sealUnary⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow sourceSeal
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
        intro row row' classified sourceRow
        exact
          ⟨sourceRow.left,
            Or.elim sourceRow.right.left
              (fun sameSeal =>
                Or.inl (hsame_trans (hsame_symm classified) sameSeal))
              (fun meshOrEnclosure =>
                Or.elim meshOrEnclosure
                  (fun sameMesh =>
                    Or.inr (Or.inl (hsame_trans (hsame_symm classified) sameMesh)))
                  (fun sameEnclosure =>
                    Or.inr (Or.inr
                      (hsame_trans (hsame_symm classified) sameEnclosure)))),
            unary_transport sourceRow.right.right classified⟩
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨commonLedgerProvenanceSeal, commonWindowProvenanceMesh,
          meshProvenanceEnclosure, sourceRow.right.right⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨sealPkg, meshPkg, enclosurePkg⟩
  }

end BEDC.Derived.DyadicApproximationUp
