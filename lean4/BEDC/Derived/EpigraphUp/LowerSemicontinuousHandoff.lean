import BEDC.Derived.EpigraphUp

namespace BEDC.Derived.EpigraphUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EpigraphLowerSemicontinuousHandoff [AskSetup] [PackageSetup]
    {D V L O H C P N queryRead lowerRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpigraphContPkgCarrier D V L O H C P N bundle pkg ->
      Cont D V queryRead ->
        Cont L O lowerRead ->
          Cont lowerRead H replayRead ->
            PkgSig bundle replayRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row lowerRead ∨ hsame row replayRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
                      hsame row H ∨ hsame row lowerRead ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont L O lowerRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle replayRead pkg)
                  hsame ∧
                UnaryHistory queryRead ∧ UnaryHistory lowerRead ∧
                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier queryRoute lowerRoute replayRoute replayPkg
  obtain ⟨dUnary, vUnary, lUnary, oUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _carrierValueRoute, _carrierTransportRoute, provenancePkg, _localNamePkg⟩ := carrier
  have queryUnary : UnaryHistory queryRead :=
    unary_cont_closed dUnary vUnary queryRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed lUnary oUnary lowerRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed lowerUnary hUnary replayRoute
  have sourceLower :
      (fun row : BHist => (hsame row lowerRead ∨ hsame row replayRead) ∧
        UnaryHistory row) lowerRead := by
    exact ⟨Or.inl (hsame_refl lowerRead), lowerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lowerRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
              hsame row H ∨ hsame row lowerRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L O lowerRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lowerRead sourceLower
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
        constructor
        · cases source.left with
          | inl sameLower =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameLower)
          | inr sameReplay =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLower =>
          right
          right
          right
          right
          right
          exact Or.inl sameLower
      | inr sameReplay =>
          right
          right
          right
          right
          right
          exact Or.inr sameReplay
    ledger_sound := by
      intro _row source
      exact ⟨source.right, lowerRoute, provenancePkg, replayPkg⟩
  }
  exact ⟨cert, queryUnary, lowerUnary, replayUnary⟩

end BEDC.Derived.EpigraphUp
