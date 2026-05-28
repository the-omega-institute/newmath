import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_window_real_seal_determinacy [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name firstSeal
      secondSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow firstSeal →
        Cont readback sealRow secondSeal →
          PkgSig bundle firstSeal pkg →
            PkgSig bundle secondSeal pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row firstSeal ∨ hsame row secondSeal) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                      hsame row readback ∨ hsame row sealRow ∨ hsame row firstSeal ∨
                        hsame row secondSeal)
                  (fun row : BHist =>
                    (hsame row firstSeal ∨ hsame row secondSeal) ∧ PkgSig bundle row pkg ∧
                      PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory firstSeal ∧ UnaryHistory secondSeal ∧
                  hsame firstSeal secondSeal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet firstSealRoute secondSealRoute firstSealPkg secondSealPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have firstSealUnary : UnaryHistory firstSeal :=
    unary_cont_closed readbackUnary sealUnary firstSealRoute
  have secondSealUnary : UnaryHistory secondSeal :=
    unary_cont_closed readbackUnary sealUnary secondSealRoute
  have firstSecondSame : hsame firstSeal secondSeal :=
    cont_respects_hsame (hsame_refl readback) (hsame_refl sealRow) firstSealRoute
      secondSealRoute
  have sourceFirstSeal :
      (fun row : BHist =>
        (hsame row firstSeal ∨ hsame row secondSeal) ∧ UnaryHistory row) firstSeal := by
    exact ⟨Or.inl (hsame_refl firstSeal), firstSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row firstSeal ∨ hsame row secondSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row firstSeal ∨
                hsame row secondSeal)
          (fun row : BHist =>
            (hsame row firstSeal ∨ hsame row secondSeal) ∧ PkgSig bundle row pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro firstSeal sourceFirstSeal
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
        | inl sameFirst =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameFirst),
                unary_transport source.right sameRows⟩
        | inr sameSecond =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameSecond),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFirst =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFirst)))))
      | inr sameSecond =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSecond)))))
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameFirst =>
          cases sameFirst
          exact ⟨Or.inl (hsame_refl firstSeal), firstSealPkg, provenancePkg⟩
      | inr sameSecond =>
          cases sameSecond
          exact ⟨Or.inr (hsame_refl secondSeal), secondSealPkg, provenancePkg⟩
  }
  exact ⟨cert, firstSealUnary, secondSealUnary, firstSecondSame⟩

end BEDC.Derived.CauchyfiltercompletionUp
