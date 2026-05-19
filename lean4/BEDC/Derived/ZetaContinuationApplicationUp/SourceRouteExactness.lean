import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_source_route_exactness [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      gammaRead operationRead sourceRead sourceRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont gamma application gammaRead →
        Cont application replay operationRead →
          Cont eta application sourceRead →
            Cont sourceRead provenance sourceRoute →
              PkgSig bundle sourceRoute pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row gammaRead ∨ hsame row operationRead ∨
                        hsame row sourceRead ∨ hsame row sourceRoute)
                    (fun _row : BHist =>
                      Cont gamma application gammaRead ∧
                        Cont application replay operationRead ∧
                          Cont eta application sourceRead ∧
                            Cont sourceRead provenance sourceRoute)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        (PkgSig bundle provenance pkg ∨ PkgSig bundle sourceRoute pkg))
                    hsame ∧
                  UnaryHistory gammaRead ∧ UnaryHistory operationRead ∧
                    UnaryHistory sourceRead ∧ UnaryHistory sourceRoute ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle sourceRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier gammaApplicationRead applicationReplayOperation etaApplicationSource
    sourceProvenanceRoute sourceRoutePkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary applicationUnary etaApplicationSource
  have sourceRouteUnary : UnaryHistory sourceRoute :=
    unary_cont_closed sourceReadUnary provenanceUnary sourceProvenanceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row gammaRead ∨ hsame row operationRead ∨ hsame row sourceRead ∨
              hsame row sourceRoute)
          (fun _row : BHist =>
            Cont gamma application gammaRead ∧ Cont application replay operationRead ∧
              Cont eta application sourceRead ∧ Cont sourceRead provenance sourceRoute)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle provenance pkg ∨ PkgSig bundle sourceRoute pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gammaRead (Or.inl (hsame_refl gammaRead))
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
        | inl sameGamma =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameGamma)
        | inr rest =>
            cases rest with
            | inl sameOperation =>
                exact
                  Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameOperation))
            | inr rest =>
                cases rest with
                | inl sameSource =>
                    exact
                      Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSource)))
                | inr sameRoute =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inr (hsame_trans (hsame_symm sameRows) sameRoute)))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨gammaApplicationRead, applicationReplayOperation, etaApplicationSource,
          sourceProvenanceRoute⟩
    ledger_sound := by
      intro row source
      cases source with
      | inl sameGamma =>
          exact
            ⟨unary_transport gammaReadUnary (hsame_symm sameGamma),
              Or.inl provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameOperation =>
              exact
                ⟨unary_transport operationReadUnary (hsame_symm sameOperation),
                  Or.inl provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameSource =>
                  exact
                    ⟨unary_transport sourceReadUnary (hsame_symm sameSource),
                      Or.inl provenancePkg⟩
              | inr sameRoute =>
                  exact
                    ⟨unary_transport sourceRouteUnary (hsame_symm sameRoute),
                      Or.inr sourceRoutePkg⟩
  }
  exact
    ⟨cert, gammaReadUnary, operationReadUnary, sourceReadUnary, sourceRouteUnary,
      provenancePkg, sourceRoutePkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
