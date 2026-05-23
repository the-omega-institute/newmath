import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_source_triad_exhaustion [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name etaRead
      gammaRead operationRead sourceReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma etaRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            Cont gammaRead operationRead sourceReplay →
              PkgSig bundle sourceReplay pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row etaRead ∨ hsame row gammaRead ∨
                        hsame row operationRead ∨ hsame row sourceReplay)
                    (fun row : BHist => UnaryHistory row)
                    (fun _row : BHist =>
                      Cont eta gamma etaRead ∧ Cont gamma application gammaRead ∧
                        Cont application replay operationRead ∧
                          Cont gammaRead operationRead sourceReplay ∧
                            PkgSig bundle sourceReplay pkg)
                    hsame ∧
                  UnaryHistory etaRead ∧ UnaryHistory gammaRead ∧
                    UnaryHistory operationRead ∧ UnaryHistory sourceReplay := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier etaGammaRead gammaApplicationRead applicationReplayRead
    gammaOperationReplay sourceReplayPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    _provenancePkg, _namePkg⟩ := carrier
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayRead
  have sourceReplayUnary : UnaryHistory sourceReplay :=
    unary_cont_closed gammaReadUnary operationReadUnary gammaOperationReplay
  have sourceEta :
      (fun row : BHist =>
        hsame row etaRead ∨ hsame row gammaRead ∨ hsame row operationRead ∨
          hsame row sourceReplay) etaRead :=
    Or.inl (hsame_refl etaRead)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row etaRead ∨ hsame row gammaRead ∨ hsame row operationRead ∨
            hsame row sourceReplay)
        (fun row : BHist => UnaryHistory row)
        (fun _row : BHist =>
          Cont eta gamma etaRead ∧ Cont gamma application gammaRead ∧
            Cont application replay operationRead ∧ Cont gammaRead operationRead sourceReplay ∧
              PkgSig bundle sourceReplay pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro etaRead sourceEta
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        cases source with
        | inl sameEta =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameEta)
        | inr rest =>
            cases rest with
            | inl sameGamma =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameGamma))
            | inr restTail =>
                cases restTail with
                | inl sameOperation =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameOperation)))
                | inr sameReplay =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameEta =>
          exact unary_transport etaReadUnary (hsame_symm sameEta)
      | inr rest =>
          cases rest with
          | inl sameGamma =>
              exact unary_transport gammaReadUnary (hsame_symm sameGamma)
          | inr restTail =>
              cases restTail with
              | inl sameOperation =>
                  exact unary_transport operationReadUnary (hsame_symm sameOperation)
              | inr sameReplay =>
                  exact unary_transport sourceReplayUnary (hsame_symm sameReplay)
    ledger_sound := by
      intro _row _source
      exact
        ⟨etaGammaRead, gammaApplicationRead, applicationReplayRead, gammaOperationReplay,
          sourceReplayPkg⟩
  }
  exact ⟨cert, etaReadUnary, gammaReadUnary, operationReadUnary, sourceReplayUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
