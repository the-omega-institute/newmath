import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_primitive_scope_package [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name sourceRead
      routeRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont sourceRead application routeRead →
          Cont routeRead provenance publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row eta ∨ hsame row gamma ∨ hsame row application ∨
                      hsame row sourceRead ∨ hsame row routeRead ∨ hsame row publicRead)
                  (fun row : BHist => UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory routeRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier etaGammaSource sourceApplicationRoute routeProvenancePublic publicReadPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sourceReadUnary applicationUnary sourceApplicationRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed routeReadUnary provenanceUnary routeProvenancePublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row eta ∨ hsame row gamma ∨ hsame row application ∨
              hsame row sourceRead ∨ hsame row routeRead ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro eta (Or.inl (hsame_refl eta))
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
                | inl sameApplication =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameApplication)))
                | inr rest =>
                    cases rest with
                    | inl sameSource =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameSource))))
                    | inr rest =>
                        cases rest with
                        | inl sameRoute =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameRoute)))))
                        | inr samePublic =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (hsame_trans (hsame_symm sameRows)
                                          samePublic)))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameEta =>
          exact unary_transport etaUnary (hsame_symm sameEta)
      | inr rest =>
          cases rest with
          | inl sameGamma =>
              exact unary_transport gammaUnary (hsame_symm sameGamma)
          | inr rest =>
              cases rest with
              | inl sameApplication =>
                  exact unary_transport applicationUnary (hsame_symm sameApplication)
              | inr rest =>
                  cases rest with
                  | inl sameSource =>
                      exact unary_transport sourceReadUnary (hsame_symm sameSource)
                  | inr rest =>
                      cases rest with
                      | inl sameRoute =>
                          exact unary_transport routeReadUnary (hsame_symm sameRoute)
                      | inr samePublic =>
                          exact unary_transport publicReadUnary (hsame_symm samePublic)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, publicReadPkg⟩
  }
  exact ⟨cert, sourceReadUnary, routeReadUnary, publicReadUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
