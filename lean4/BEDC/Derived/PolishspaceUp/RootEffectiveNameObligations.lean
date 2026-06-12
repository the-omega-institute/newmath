import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceRootEffectiveNameObligations [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      effectiveName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier metric complete separable stream readback
        ledger transport replay provenance localName bundle pkg ->
      Cont stream readback effectiveName ->
        PkgSig bundle effectiveName pkg ->
          SemanticNameCert
              (fun row : BHist =>
                (hsame row stream ∨ hsame row readback ∨ hsame row effectiveName) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                  hsame row effectiveName)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle effectiveName pkg)
              hsame ∧ UnaryHistory effectiveName := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier effectiveRoute effectivePkg
  obtain ⟨_metricUnary, _completeUnary, _separableUnary, streamUnary, readbackUnary,
    _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _metricCompleteLedger, _ledgerStreamReadback, _transportReplayProvenance,
    provenancePkg, localNamePkg⟩ := carrier
  have effectiveUnary : UnaryHistory effectiveName :=
    unary_cont_closed streamUnary readbackUnary effectiveRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row stream ∨ hsame row readback ∨ hsame row effectiveName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
              hsame row effectiveName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle effectiveName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro effectiveName
          ⟨Or.inr (Or.inr (hsame_refl effectiveName)), effectiveUnary⟩
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
        have sourceRoute :
            hsame _other stream ∨ hsame _other readback ∨ hsame _other effectiveName := by
          cases source.left with
          | inl streamSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) streamSame)
          | inr tail =>
              cases tail with
              | inl readbackSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) readbackSame))
              | inr effectiveSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) effectiveSame))
        exact ⟨sourceRoute, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl streamSame =>
          exact Or.inl streamSame
      | inr tail =>
          cases tail with
          | inl readbackSame =>
              exact Or.inr (Or.inl readbackSame)
          | inr effectiveSame =>
              exact Or.inr (Or.inr (Or.inr effectiveSame))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, effectivePkg⟩
  }
  exact ⟨cert, effectiveUnary⟩

end BEDC.Derived.PolishspaceUp
