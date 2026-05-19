import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_visible_boundary_lock [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name etaRead
      poleRead zeroRead gammaRead operationRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      hsame etaRead eta →
        Cont pole zeroLedger poleRead →
          Cont zeroLedger gamma zeroRead →
            Cont gamma application gammaRead →
              Cont application replay operationRead →
                Cont provenance name boundaryRead →
                  PkgSig bundle operationRead pkg →
                    PkgSig bundle boundaryRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row etaRead ∨ hsame row gammaRead ∨
                              hsame row operationRead ∨ hsame row boundaryRead)
                          (fun _row : BHist =>
                            Cont gamma application gammaRead ∧
                              Cont application replay operationRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧
                              (PkgSig bundle operationRead pkg ∨
                                PkgSig bundle boundaryRead pkg))
                          hsame ∧
                        UnaryHistory etaRead ∧ UnaryHistory poleRead ∧
                          UnaryHistory zeroRead ∧ UnaryHistory gammaRead ∧
                            UnaryHistory operationRead ∧ UnaryHistory boundaryRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle operationRead pkg ∧
                                  PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier etaReadSame poleZeroRead zeroGammaRead gammaApplicationRead
    applicationReplayOperation provenanceNameBoundary operationPkg boundaryPkg
  obtain ⟨etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaReadUnary : UnaryHistory etaRead :=
    unary_transport etaUnary (hsame_symm etaReadSame)
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroRead
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroLedgerUnary gammaUnary zeroGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row etaRead ∨ hsame row gammaRead ∨ hsame row operationRead ∨
              hsame row boundaryRead)
          (fun _row : BHist =>
            Cont gamma application gammaRead ∧ Cont application replay operationRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle operationRead pkg ∨ PkgSig bundle boundaryRead pkg))
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
                exact Or.inr
                  (Or.inl (hsame_trans (hsame_symm sameRows) sameGamma))
            | inr rest =>
                cases rest with
                | inl sameOperation =>
                    exact Or.inr
                      (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameOperation)))
                | inr sameBoundary =>
                    exact Or.inr
                      (Or.inr
                        (Or.inr (hsame_trans (hsame_symm sameRows) sameBoundary)))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨gammaApplicationRead, applicationReplayOperation⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameEta =>
          exact ⟨unary_transport etaReadUnary (hsame_symm sameEta), Or.inl operationPkg⟩
      | inr rest =>
          cases rest with
          | inl sameGamma =>
              exact
                ⟨unary_transport gammaReadUnary (hsame_symm sameGamma),
                  Or.inl operationPkg⟩
          | inr rest =>
              cases rest with
              | inl sameOperation =>
                  exact
                    ⟨unary_transport operationReadUnary (hsame_symm sameOperation),
                      Or.inl operationPkg⟩
              | inr sameBoundary =>
                  exact
                    ⟨unary_transport boundaryReadUnary (hsame_symm sameBoundary),
                      Or.inr boundaryPkg⟩
  }
  exact
    ⟨cert, etaReadUnary, poleReadUnary, zeroReadUnary, gammaReadUnary, operationReadUnary,
      boundaryReadUnary, provenancePkg, operationPkg, boundaryPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
