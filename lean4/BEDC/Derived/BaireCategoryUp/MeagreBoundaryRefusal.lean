import BEDC.Derived.BaireCategoryUp.NameCertObligations

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_meagre_boundary_refusal [AskSetup] [PackageSetup]
    {B M D O R T H C P N terminal meagreBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont D O meagreBoundary ->
        Cont T M terminal ->
          PkgSig bundle meagreBoundary pkg ->
            PkgSig bundle terminal pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row meagreBoundary ∨ hsame row terminal)
                    (fun row : BHist => UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧
                        (hsame row meagreBoundary ∨ hsame row terminal))
                    hsame ∧
                  UnaryHistory meagreBoundary ∧ UnaryHistory terminal ∧
                    baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
                      [B, M, D, O, R, T, H, C, P, N] := by
  -- BEDC touchpoint anchor: BaireCategoryCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier boundaryRoute terminalRoute _boundaryPkg _terminalPkg
  obtain ⟨_baseUnary, metricUnary, denseUnary, openUnary, _refinementUnary, threadUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory meagreBoundary :=
    unary_cont_closed denseUnary openUnary boundaryRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed threadUnary metricUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row meagreBoundary ∨ hsame row terminal)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row meagreBoundary ∨ hsame row terminal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro meagreBoundary (Or.inl (hsame_refl meagreBoundary))
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
        cases source with
        | inl sameBoundary =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary)
        | inr sameTerminal =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameTerminal)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameBoundary =>
          exact unary_transport boundaryUnary (hsame_symm sameBoundary)
      | inr sameTerminal =>
          exact unary_transport terminalUnary (hsame_symm sameTerminal)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source⟩
  }
  exact ⟨cert, boundaryUnary, terminalUnary, rfl⟩

end BEDC.Derived.BaireCategoryUp
