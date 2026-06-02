import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisRefinementFactorization [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M hitRead missRead refinementRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 N0 hitRead ->
        Cont K1 N1 missRead ->
          Cont hitRead missRead refinementRead ->
            Cont Hs C replayRead ->
              PkgSig bundle refinementRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row refinementRead ∨ hsame row replayRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨ hsame row N1 ∨
                        hsame row hitRead ∨ hsame row missRead ∨
                          hsame row refinementRead ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont hitRead missRead refinementRead ∧
                        PkgSig bundle refinementRead pkg)
                    hsame ∧
                  UnaryHistory hitRead ∧ UnaryHistory missRead ∧
                    UnaryHistory refinementRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier hitRoute missRoute refinementRoute replayRoute refinementPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    _rUnary, hsUnary, cUnary, _pUnary, _mUnary, _provenancePkg⟩ := carrier
  have hitUnary : UnaryHistory hitRead :=
    unary_cont_closed k0Unary n0Unary hitRoute
  have missUnary : UnaryHistory missRead :=
    unary_cont_closed k1Unary n1Unary missRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed hitUnary missUnary refinementRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row refinementRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨ hsame row N1 ∨
              hsame row hitRead ∨ hsame row missRead ∨ hsame row refinementRead ∨
                hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont hitRead missRead refinementRead ∧
              PkgSig bundle refinementRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinementRead
          ⟨Or.inl (hsame_refl refinementRead), refinementUnary⟩
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
          | inl sameRefinement =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameRefinement)
          | inr sameReplay =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRefinement =>
          right
          right
          right
          right
          right
          right
          exact Or.inl sameRefinement
      | inr sameReplay =>
          right
          right
          right
          right
          right
          right
          exact Or.inr sameReplay
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refinementRoute, refinementPkg⟩
  }
  exact ⟨cert, hitUnary, missUnary, refinementUnary, replayUnary⟩

end BEDC.Derived.HyperspaceUp
