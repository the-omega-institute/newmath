import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Hyperspace_vietoris_handoff [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M hitRead missRead vietorisRead
      hausdorffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 N0 hitRead ->
        Cont K1 N1 missRead ->
          Cont hitRead missRead vietorisRead ->
            Cont D0 D1 hausdorffRead ->
              PkgSig bundle vietorisRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row vietorisRead ∨ hsame row hausdorffRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                        hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨
                          hsame row vietorisRead ∨ hsame row hausdorffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle vietorisRead pkg)
                    hsame ∧
                  UnaryHistory hitRead ∧ UnaryHistory missRead ∧
                    UnaryHistory vietorisRead ∧ UnaryHistory hausdorffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier hitRoute missRoute vietorisRoute hausdorffRoute vietorisPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have hitUnary : UnaryHistory hitRead :=
    unary_cont_closed k0Unary n0Unary hitRoute
  have missUnary : UnaryHistory missRead :=
    unary_cont_closed k1Unary n1Unary missRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed hitUnary missUnary vietorisRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed d0Unary d1Unary hausdorffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row vietorisRead ∨ hsame row hausdorffRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨ hsame row N1 ∨
              hsame row D0 ∨ hsame row D1 ∨ hsame row vietorisRead ∨
                hsame row hausdorffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle vietorisRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro vietorisRead ⟨Or.inl (hsame_refl vietorisRead), vietorisUnary⟩
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
          | inl sameVietoris =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameVietoris)
          | inr sameHausdorff =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameHausdorff)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameVietoris =>
          right
          right
          right
          right
          right
          right
          left
          exact sameVietoris
      | inr sameHausdorff =>
          right
          right
          right
          right
          right
          right
          right
          exact sameHausdorff
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, vietorisPkg⟩
  }
  exact ⟨cert, hitUnary, missUnary, vietorisUnary, hausdorffUnary⟩

end BEDC.Derived.HyperspaceUp
