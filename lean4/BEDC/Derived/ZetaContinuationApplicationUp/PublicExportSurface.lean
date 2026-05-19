import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_public_export_surface [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name sourceRead
      gammaRead operationRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            Cont provenance name ledgerRead →
              Cont operationRead ledgerRead publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row sourceRead ∨ hsame row gammaRead ∨
                          hsame row operationRead ∨ hsame row ledgerRead ∨
                            hsame row publicRead)
                      (fun row : BHist => UnaryHistory row)
                      (fun _row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory sourceRead ∧ UnaryHistory gammaRead ∧
                      UnaryHistory operationRead ∧ UnaryHistory ledgerRead ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier etaGammaSource gammaApplicationRead applicationReplayOperation
    provenanceNameLedger operationLedgerPublic publicReadPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameLedger
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed operationReadUnary ledgerReadUnary operationLedgerPublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row gammaRead ∨ hsame row operationRead ∨
              hsame row ledgerRead ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead (Or.inl (hsame_refl sourceRead))
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
        | inl sameSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
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
                | inr rest =>
                    cases rest with
                    | inl sameLedger =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameLedger))))
                    | inr samePublic =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) samePublic))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameSource =>
          exact unary_transport sourceReadUnary (hsame_symm sameSource)
      | inr rest =>
          cases rest with
          | inl sameGamma =>
              exact unary_transport gammaReadUnary (hsame_symm sameGamma)
          | inr rest =>
              cases rest with
              | inl sameOperation =>
                  exact unary_transport operationReadUnary (hsame_symm sameOperation)
              | inr rest =>
                  cases rest with
                  | inl sameLedger =>
                      exact unary_transport ledgerReadUnary (hsame_symm sameLedger)
                  | inr samePublic =>
                      exact unary_transport publicReadUnary (hsame_symm samePublic)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, publicReadPkg⟩
  }
  exact
    ⟨cert, sourceReadUnary, gammaReadUnary, operationReadUnary, ledgerReadUnary,
      publicReadUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
