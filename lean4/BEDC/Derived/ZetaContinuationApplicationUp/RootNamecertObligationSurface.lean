import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name etaRead
      gammaRead operationRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg ->
      Cont eta gamma etaRead ->
        Cont gamma application gammaRead ->
          Cont application replay operationRead ->
            Cont provenance name ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row etaRead ∨ hsame row gammaRead ∨
                        hsame row operationRead ∨ hsame row ledgerRead)
                    (fun _row : BHist =>
                      Cont eta gamma etaRead ∧ Cont gamma application gammaRead ∧
                        Cont application replay operationRead ∧
                          Cont provenance name ledgerRead)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle ledgerRead pkg)
                    hsame ∧
                  UnaryHistory etaRead ∧ UnaryHistory gammaRead ∧
                    UnaryHistory operationRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier etaGammaRead gammaApplicationRead applicationReplayOperation
    provenanceNameLedgerRead ledgerReadPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    _provenancePkg, _namePkg⟩ := carrier
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameLedgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row etaRead ∨ hsame row gammaRead ∨ hsame row operationRead ∨
              hsame row ledgerRead)
          (fun _row : BHist =>
            Cont eta gamma etaRead ∧ Cont gamma application gammaRead ∧
              Cont application replay operationRead ∧ Cont provenance name ledgerRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro etaRead (Or.inl (hsame_refl etaRead))
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
        cases source with
        | inl sameEta =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameEta)
        | inr rest =>
            cases rest with
            | inl sameGamma =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameGamma))
            | inr rest =>
                cases rest with
                | inl sameOperation =>
                    exact Or.inr
                      (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameOperation)))
                | inr sameLedger =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLedger)))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨etaGammaRead, gammaApplicationRead, applicationReplayOperation,
          provenanceNameLedgerRead⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameEta =>
          exact ⟨unary_transport etaReadUnary (hsame_symm sameEta), ledgerReadPkg⟩
      | inr rest =>
          cases rest with
          | inl sameGamma =>
              exact ⟨unary_transport gammaReadUnary (hsame_symm sameGamma), ledgerReadPkg⟩
          | inr rest =>
              cases rest with
              | inl sameOperation =>
                  exact
                    ⟨unary_transport operationReadUnary (hsame_symm sameOperation),
                      ledgerReadPkg⟩
              | inr sameLedger =>
                  exact ⟨unary_transport ledgerReadUnary (hsame_symm sameLedger), ledgerReadPkg⟩
  }
  exact ⟨cert, etaReadUnary, gammaReadUnary, operationReadUnary, ledgerReadUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
