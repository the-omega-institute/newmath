import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg ->
      (hsame ledgerRead pole ∨ hsame ledgerRead zeroLedger ∨ hsame ledgerRead gamma ∨
        hsame ledgerRead provenance ∨ hsame ledgerRead name) ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma
                    application transport replay provenance name bundle pkg ∧
                  hsame row ledgerRead)
              (fun row : BHist =>
                hsame row pole ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                  hsame row provenance ∨ hsame row name ∨ hsame row ledgerRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier ledgerSurface ledgerPkg
  have carrierPacket :
      ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application
        transport replay provenance name bundle pkg :=
    carrier
  obtain ⟨_etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    _applicationUnary, _transportUnary, _replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    _provenancePkg, _namePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead := by
    cases ledgerSurface with
    | inl samePole =>
        exact unary_transport poleUnary (hsame_symm samePole)
    | inr rest =>
        cases rest with
        | inl sameZero =>
            exact unary_transport zeroLedgerUnary (hsame_symm sameZero)
        | inr rest =>
            cases rest with
            | inl sameGamma =>
                exact unary_transport gammaUnary (hsame_symm sameGamma)
            | inr rest =>
                cases rest with
                | inl sameProvenance =>
                    exact unary_transport provenanceUnary (hsame_symm sameProvenance)
                | inr sameName =>
                    exact unary_transport nameUnary (hsame_symm sameName)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma
                application transport replay provenance name bundle pkg ∧
              hsame row ledgerRead)
          (fun row : BHist =>
            hsame row pole ∨ hsame row zeroLedger ∨ hsame row gamma ∨
              hsame row provenance ∨ hsame row name ∨ hsame row ledgerRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨carrierPacket, hsame_refl ledgerRead⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      cases ledgerSurface with
      | inl samePole =>
          exact Or.inl (hsame_trans source.right samePole)
      | inr rest =>
          cases rest with
          | inl sameZero =>
              exact Or.inr (Or.inl (hsame_trans source.right sameZero))
          | inr rest =>
              cases rest with
              | inl sameGamma =>
                  exact Or.inr (Or.inr (Or.inl (hsame_trans source.right sameGamma)))
              | inr rest =>
                  cases rest with
                  | inl sameProvenance =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans source.right sameProvenance))))
                  | inr sameName =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans source.right sameName)))))
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport ledgerUnary (hsame_symm source.right), ledgerPkg⟩
  }
  exact ⟨cert, ledgerUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
