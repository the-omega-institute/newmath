import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_four_face_nocollapse [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              SemanticNameCert
                (fun row : BHist =>
                  CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                    (hsame row t ∨ hsame row w ∨ hsame row q ∨ hsame row e))
                (fun row : BHist =>
                  Cont t w selected ∧ Cont selected q readback ∧
                    Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                      (hsame row t ∨ hsame row w ∨ hsame row q ∨ hsame row e))
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  let carrierPacket :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro t (And.intro carrierPacket (Or.inl (hsame_refl t)))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro row row' same source
        rcases source with ⟨sourceCarrier, sourceFace⟩
        refine And.intro sourceCarrier ?_
        cases sourceFace with
        | inl rowT =>
            exact Or.inl (hsame_trans (hsame_symm same) rowT)
        | inr rest =>
            cases rest with
            | inl rowW =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowW))
            | inr restTail =>
                cases restTail with
                | inl rowQ =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowQ)))
                | inr rowE =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm same) rowE)))
    }
    pattern_sound := by
      intro row source
      exact ⟨tWSelected, selectedQReadback, readbackESeal, sealHPublic, source.right⟩
    ledger_sound := by
      intro row source
      rcases source with ⟨_sourceCarrier, sourceFace⟩
      cases sourceFace with
      | inl rowT =>
          exact ⟨unary_transport tUnary (hsame_symm rowT), pPkg⟩
      | inr rest =>
          cases rest with
          | inl rowW =>
              exact ⟨unary_transport wUnary (hsame_symm rowW), pPkg⟩
          | inr restTail =>
              cases restTail with
              | inl rowQ =>
                  exact ⟨unary_transport qUnary (hsame_symm rowQ), pPkg⟩
              | inr rowE =>
                  exact ⟨unary_transport eUnary (hsame_symm rowE), pPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
