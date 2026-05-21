import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_obligation_readiness [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      etaFunctionalRead gammaApplicationRead applicationReplayRead ledgerRoute
      rootObligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta functional etaFunctionalRead →
        Cont gamma application gammaApplicationRead →
          Cont application replay applicationReplayRead →
            Cont provenance name ledgerRoute →
              Cont etaFunctionalRead ledgerRoute rootObligationRead →
                PkgSig bundle rootObligationRead pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row etaFunctionalRead ∨ hsame row gammaApplicationRead ∨
                        hsame row applicationReplayRead ∨ hsame row ledgerRoute ∨
                          hsame row rootObligationRead)
                    (fun row : BHist => UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier etaFunctionalRoute gammaApplicationRoute applicationReplayRoute
    provenanceNameRoute rootObligationRoute rootObligationPkg
  obtain ⟨etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaFunctionalReadUnary : UnaryHistory etaFunctionalRead :=
    unary_cont_closed etaUnary functionalUnary etaFunctionalRoute
  have gammaApplicationReadUnary : UnaryHistory gammaApplicationRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRoute
  have applicationReplayReadUnary : UnaryHistory applicationReplayRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayRoute
  have ledgerRouteUnary : UnaryHistory ledgerRoute :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameRoute
  have rootObligationReadUnary : UnaryHistory rootObligationRead :=
    unary_cont_closed etaFunctionalReadUnary ledgerRouteUnary rootObligationRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro rootObligationRead
        (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl rootObligationRead)))))
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
        | inl sameEtaFunctional =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameEtaFunctional)
        | inr rest =>
            cases rest with
            | inl sameGammaApplication =>
                exact Or.inr
                  (Or.inl (hsame_trans (hsame_symm sameRows) sameGammaApplication))
            | inr rest =>
                cases rest with
                | inl sameApplicationReplay =>
                    exact Or.inr
                      (Or.inr
                        (Or.inl
                          (hsame_trans (hsame_symm sameRows) sameApplicationReplay)))
                | inr rest =>
                    cases rest with
                    | inl sameLedger =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameLedger))))
                    | inr sameRoot =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) sameRoot))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameEtaFunctional =>
          exact unary_transport etaFunctionalReadUnary (hsame_symm sameEtaFunctional)
      | inr rest =>
          cases rest with
          | inl sameGammaApplication =>
              exact unary_transport gammaApplicationReadUnary (hsame_symm sameGammaApplication)
          | inr rest =>
              cases rest with
              | inl sameApplicationReplay =>
                  exact
                    unary_transport applicationReplayReadUnary
                      (hsame_symm sameApplicationReplay)
              | inr rest =>
                  cases rest with
                  | inl sameLedger =>
                      exact unary_transport ledgerRouteUnary (hsame_symm sameLedger)
                  | inr sameRoot =>
                      exact unary_transport rootObligationReadUnary (hsame_symm sameRoot)
    ledger_sound := by
      intro _row source
      cases source with
      | inl _sameEtaFunctional =>
          exact Or.inl provenancePkg
      | inr rest =>
          cases rest with
          | inl _sameGammaApplication =>
              exact Or.inl provenancePkg
          | inr rest =>
              cases rest with
              | inl _sameApplicationReplay =>
                  exact Or.inl provenancePkg
              | inr rest =>
                  cases rest with
                  | inl _sameLedger =>
                      exact Or.inl provenancePkg
                  | inr sameRoot =>
                      exact Or.inr
                        (by
                          cases sameRoot
                          exact rootObligationPkg)
  }

end BEDC.Derived.ZetaContinuationApplicationUp
