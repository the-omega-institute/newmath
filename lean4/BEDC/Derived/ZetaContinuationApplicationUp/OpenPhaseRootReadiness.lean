import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_open_phase_root_readiness [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name etaRead
      gammaRead applicationRead openRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma etaRead →
        Cont gamma application gammaRead →
          Cont application replay applicationRead →
            Cont etaRead applicationRead openRead →
              PkgSig bundle openRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row etaRead ∨ hsame row gammaRead ∨
                        hsame row applicationRead ∨ hsame row openRead)
                    (fun row : BHist => UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
                    hsame ∧
                  UnaryHistory openRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier etaGammaRead gammaApplicationRead applicationReplayRead openPhaseRead
    _openReadPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have applicationReadUnary : UnaryHistory applicationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayRead
  have openReadUnary : UnaryHistory openRead :=
    unary_cont_closed etaReadUnary applicationReadUnary openPhaseRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row etaRead ∨ hsame row gammaRead ∨ hsame row applicationRead ∨
              hsame row openRead)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro etaRead (Or.inl (hsame_refl etaRead))
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
        intro _row _other sameRows source
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
                      (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameApplication)))
                | inr sameOpen =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameOpen)))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameEta =>
          exact unary_transport etaReadUnary (hsame_symm sameEta)
      | inr rest =>
          cases rest with
          | inl sameGamma =>
              exact unary_transport gammaReadUnary (hsame_symm sameGamma)
          | inr rest =>
              cases rest with
              | inl sameApplication =>
                  exact unary_transport applicationReadUnary (hsame_symm sameApplication)
              | inr sameOpen =>
                  exact unary_transport openReadUnary (hsame_symm sameOpen)
    ledger_sound := by
      intro _row _source
      exact Or.inl provenancePkg
  }
  exact ⟨cert, openReadUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
