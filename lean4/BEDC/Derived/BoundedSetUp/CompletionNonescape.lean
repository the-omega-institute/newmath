import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_completion_nonescape [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead replay completionRead ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row S ∨ hsame row radius ∨ hsame row ballRead ∨
                      hsame row completionRead ∨ Cont ballRead replay completionRead)
                  (fun row : BHist => PkgSig bundle completionRead pkg ∧ hsame row completionRead)
                  hsame ∧
                UnaryHistory memberRead ∧ UnaryHistory ballRead ∧ UnaryHistory completionRead ∧
                  Cont S center memberRead ∧ Cont memberRead radius ballRead ∧
                    Cont ballRead replay completionRead ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier subsetCenter memberRadius ballReplayCompletion completionPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    _provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed ballReadUnary replayUnary ballReplayCompletion
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row radius ∨ hsame row ballRead ∨
              hsame row completionRead ∨ Cont ballRead replay completionRead)
          (fun row : BHist => PkgSig bundle completionRead pkg ∧ hsame row completionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨completionPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, ballReadUnary, completionUnary, subsetCenter, memberRadius,
      ballReplayCompletion, completionPkg⟩

end BEDC.Derived.BoundedSetUp
