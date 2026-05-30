import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_source_lock [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      sourceRead gammaRead operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            PkgSig bundle operationRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row eta ∨ hsame row gamma ∨ hsame row application ∨
                      hsame row sourceRead ∨ hsame row gammaRead ∨ hsame row operationRead)
                  (fun _row : BHist =>
                    Cont eta gamma sourceRead ∧ Cont gamma application gammaRead ∧
                      Cont application replay operationRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle provenance pkg ∨ PkgSig bundle operationRead pkg))
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory gammaRead ∧
                  UnaryHistory operationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier etaGammaSource gammaApplicationRead applicationReplayOperation operationPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row eta ∨ hsame row gamma ∨ hsame row application ∨
              hsame row sourceRead ∨ hsame row gammaRead ∨ hsame row operationRead)
          (fun _row : BHist =>
            Cont eta gamma sourceRead ∧ Cont gamma application gammaRead ∧
              Cont application replay operationRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle provenance pkg ∨ PkgSig bundle operationRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead
        (Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl sourceRead)))))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
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
                | inl sameApplication =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameApplication)))
                | inr rest =>
                    cases rest with
                    | inl sameSource =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameSource))))
                    | inr rest =>
                        cases rest with
                        | inl sameGammaRead =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameGammaRead)))))
                        | inr sameOperation =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (hsame_trans (hsame_symm sameRows) sameOperation)))))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨etaGammaSource, gammaApplicationRead, applicationReplayOperation⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameEta =>
          exact ⟨unary_transport etaUnary (hsame_symm sameEta), Or.inl provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameGamma =>
              exact
                ⟨unary_transport gammaUnary (hsame_symm sameGamma), Or.inl provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameApplication =>
                  exact
                    ⟨unary_transport applicationUnary (hsame_symm sameApplication),
                      Or.inl provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameSource =>
                      exact
                        ⟨unary_transport sourceReadUnary (hsame_symm sameSource),
                          Or.inr operationPkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameGammaRead =>
                          exact
                            ⟨unary_transport gammaReadUnary (hsame_symm sameGammaRead),
                              Or.inr operationPkg⟩
                      | inr sameOperation =>
                          exact
                            ⟨unary_transport operationReadUnary (hsame_symm sameOperation),
                              Or.inr operationPkg⟩
  }
  exact ⟨cert, sourceReadUnary, gammaReadUnary, operationReadUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
