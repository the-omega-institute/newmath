import BEDC.Derived.RepresentedSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_translation_nonescape [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName translationRead
      targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont name schedule translationRead →
        Cont target localName targetRead →
          PkgSig bundle translationRead pkg →
            PkgSig bundle targetRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row translationRead ∨ hsame row targetRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                      hsame row target ∨ hsame row translationRead ∨ hsame row targetRead)
                  (fun row : BHist =>
                    (hsame row translationRead ∨ hsame row targetRead) ∧
                      PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory translationRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameScheduleTranslation targetLocalNameRead translationReadPkg targetReadPkg
  obtain ⟨nameUnary, scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have translationReadUnary : UnaryHistory translationRead :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleTranslation
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalNameRead
  have sourceTranslationRead :
      (fun row : BHist =>
        (hsame row translationRead ∨ hsame row targetRead) ∧ UnaryHistory row)
          translationRead := by
    exact ⟨Or.inl (hsame_refl translationRead), translationReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row translationRead ∨ hsame row targetRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row translationRead ∨ hsame row targetRead)
          (fun row : BHist =>
            (hsame row translationRead ∨ hsame row targetRead) ∧
              PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro translationRead sourceTranslationRead
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
        cases source.left with
        | inl sameTranslation =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameTranslation),
                unary_transport source.right sameRows⟩
        | inr sameTarget =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameTarget),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameTranslation =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameTranslation))))
      | inr sameTarget =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameTarget))))
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameTranslation =>
          cases sameTranslation
          exact ⟨Or.inl (hsame_refl translationRead), translationReadPkg, provenancePkg⟩
      | inr sameTarget =>
          cases sameTarget
          exact ⟨Or.inr (hsame_refl targetRead), targetReadPkg, provenancePkg⟩
  }
  exact ⟨cert, translationReadUnary, targetReadUnary⟩

end BEDC.Derived.RepresentedSpaceUp
