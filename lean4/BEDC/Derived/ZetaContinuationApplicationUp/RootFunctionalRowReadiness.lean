import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_functional_row_readiness [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      functionalRead replayRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont functional gamma functionalRead →
        Cont functionalRead replay replayRead →
          Cont replayRead provenance rootRead →
            PkgSig bundle rootRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row functionalRead ∨ hsame row replayRead ∨ hsame row rootRead)
                  (fun row : BHist => UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
                  hsame ∧
                UnaryHistory functionalRead ∧ UnaryHistory replayRead ∧
                  UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier functionalGammaRead functionalReadReplay replayReadProvenance rootPkg
  obtain ⟨_etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    _applicationUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed functionalUnary gammaUnary functionalGammaRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed functionalReadUnary replayUnary functionalReadReplay
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed replayReadUnary provenanceUnary replayReadProvenance
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row functionalRead ∨ hsame row replayRead ∨ hsame row rootRead)
        (fun row : BHist => UnaryHistory row)
        (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rootRead (Or.inr (Or.inr (hsame_refl rootRead)))
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
        | inl sameFunctional =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameFunctional)
        | inr tail =>
            cases tail with
            | inl sameReplay =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameReplay))
            | inr sameRoot =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameRoot))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameFunctional =>
          exact unary_transport functionalReadUnary (hsame_symm sameFunctional)
      | inr tail =>
          cases tail with
          | inl sameReplay =>
              exact unary_transport replayReadUnary (hsame_symm sameReplay)
          | inr sameRoot =>
              exact unary_transport rootReadUnary (hsame_symm sameRoot)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, rootPkg⟩
  }
  exact ⟨cert, functionalReadUnary, replayReadUnary, rootReadUnary⟩

end BEDC.Derived.ZetaContinuationApplicationUp
