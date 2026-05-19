import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_ledger_boundary [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name poleRead
      zeroRead gammaRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg ->
      Cont pole zeroLedger poleRead ->
        Cont zeroLedger gamma zeroRead ->
          Cont gamma application gammaRead ->
            Cont provenance name ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row poleRead ∨ hsame row zeroRead ∨ hsame row gammaRead ∨
                        hsame row ledgerRead)
                    (fun _row : BHist =>
                      Cont pole zeroLedger poleRead ∧ Cont zeroLedger gamma zeroRead ∧
                        Cont gamma application gammaRead ∧ Cont provenance name ledgerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        (PkgSig bundle provenance pkg ∨ PkgSig bundle ledgerRead pkg))
                    hsame ∧
                  UnaryHistory poleRead ∧ UnaryHistory zeroRead ∧ UnaryHistory gammaRead ∧
                    UnaryHistory ledgerRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier poleZeroRead zeroGammaRead gammaApplicationRead provenanceNameLedgerRead
    ledgerReadPkg
  obtain ⟨_etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroRead
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroLedgerUnary gammaUnary zeroGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameLedgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row poleRead ∨ hsame row zeroRead ∨ hsame row gammaRead ∨
              hsame row ledgerRead)
          (fun _row : BHist =>
            Cont pole zeroLedger poleRead ∧ Cont zeroLedger gamma zeroRead ∧
              Cont gamma application gammaRead ∧ Cont provenance name ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle provenance pkg ∨ PkgSig bundle ledgerRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro poleRead (Or.inl (hsame_refl poleRead))
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
        | inl samePole =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) samePole)
        | inr rest =>
            cases rest with
            | inl sameZero =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameZero))
            | inr rest =>
                cases rest with
                | inl sameGamma =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameGamma)))
                | inr sameLedger =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLedger)))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨poleZeroRead, zeroGammaRead, gammaApplicationRead, provenanceNameLedgerRead⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl samePole =>
          exact ⟨unary_transport poleReadUnary (hsame_symm samePole),
            Or.inl provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameZero =>
              exact ⟨unary_transport zeroReadUnary (hsame_symm sameZero),
                Or.inl provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameGamma =>
                  exact ⟨unary_transport gammaReadUnary (hsame_symm sameGamma),
                    Or.inl provenancePkg⟩
              | inr sameLedger =>
                  exact ⟨unary_transport ledgerReadUnary (hsame_symm sameLedger),
                    Or.inr ledgerReadPkg⟩
  }
  exact ⟨cert, poleReadUnary, zeroReadUnary, gammaReadUnary, ledgerReadUnary, provenancePkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
