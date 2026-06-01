import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisDownstreamDependency [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M hitRead missRead directedRead hausdorffRead
      vietorisRead compactMetricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 N0 hitRead →
        Cont K1 N1 missRead →
          Cont D0 D1 directedRead →
            Cont directedRead R hausdorffRead →
              Cont hitRead missRead vietorisRead →
                Cont X M compactMetricRead →
                  PkgSig bundle hausdorffRead pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        (hsame row vietorisRead ∨ hsame row hausdorffRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                          hsame row N0 ∨ hsame row N1 ∨ hsame row D0 ∨
                            hsame row D1 ∨ hsame row R ∨
                              hsame row compactMetricRead ∨ hsame row vietorisRead ∨
                                hsame row hausdorffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle hausdorffRead pkg)
                      hsame ∧
                      UnaryHistory hitRead ∧ UnaryHistory missRead ∧
                        UnaryHistory directedRead ∧ UnaryHistory hausdorffRead ∧
                          UnaryHistory vietorisRead ∧ UnaryHistory compactMetricRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier hitRoute missRoute directedRoute hausdorffRoute vietorisRoute
    compactMetricRoute hausdorffPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, mUnary, provenancePkg⟩ := carrier
  have hitUnary : UnaryHistory hitRead :=
    unary_cont_closed k0Unary n0Unary hitRoute
  have missUnary : UnaryHistory missRead :=
    unary_cont_closed k1Unary n1Unary missRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed d0Unary d1Unary directedRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed directedUnary rUnary hausdorffRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed hitUnary missUnary vietorisRoute
  have compactMetricUnary : UnaryHistory compactMetricRead :=
    unary_cont_closed xUnary mUnary compactMetricRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          (hsame row vietorisRead ∨ hsame row hausdorffRead) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
            hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
              hsame row compactMetricRead ∨ hsame row vietorisRead ∨
                hsame row hausdorffRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle hausdorffRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro vietorisRead
          ⟨Or.inl (hsame_refl vietorisRead), vietorisUnary⟩
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
        intro row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameVietoris =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameVietoris),
                otherUnary⟩
        | inr sameHausdorff =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameHausdorff),
                otherUnary⟩
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
          right
          right
          right
          exact sameHausdorff
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, hausdorffPkg⟩
  }
  exact
    ⟨cert, hitUnary, missUnary, directedUnary, hausdorffUnary, vietorisUnary,
      compactMetricUnary⟩

theorem HyperspaceVietorisCompactMetricDependency [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M hitRead missRead directedRead hausdorffRead
      vietorisRead compactMetricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 N0 hitRead ->
        Cont K1 N1 missRead ->
          Cont D0 D1 directedRead ->
            Cont directedRead R hausdorffRead ->
              Cont hitRead missRead vietorisRead ->
                Cont X M compactMetricRead ->
                  PkgSig bundle vietorisRead pkg ->
                    PkgSig bundle hausdorffRead pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row compactMetricRead ∨ hsame row vietorisRead ∨
                              hsame row hausdorffRead) ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                              hsame row N0 ∨ hsame row N1 ∨ hsame row D0 ∨
                                hsame row D1 ∨ hsame row R ∨
                                  hsame row compactMetricRead ∨ hsame row vietorisRead ∨
                                    hsame row hausdorffRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle vietorisRead pkg ∧
                                PkgSig bundle hausdorffRead pkg)
                          hsame ∧
                        UnaryHistory compactMetricRead ∧ UnaryHistory vietorisRead ∧
                          UnaryHistory hausdorffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier hitRoute missRoute directedRoute hausdorffRoute vietorisRoute
    compactMetricRoute vietorisPkg hausdorffPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, mUnary, provenancePkg⟩ := carrier
  have hitUnary : UnaryHistory hitRead :=
    unary_cont_closed k0Unary n0Unary hitRoute
  have missUnary : UnaryHistory missRead :=
    unary_cont_closed k1Unary n1Unary missRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed d0Unary d1Unary directedRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed directedUnary rUnary hausdorffRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed hitUnary missUnary vietorisRoute
  have compactMetricUnary : UnaryHistory compactMetricRead :=
    unary_cont_closed xUnary mUnary compactMetricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row compactMetricRead ∨ hsame row vietorisRead ∨
              hsame row hausdorffRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row compactMetricRead ∨ hsame row vietorisRead ∨
                  hsame row hausdorffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle vietorisRead pkg ∧
              PkgSig bundle hausdorffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compactMetricRead
          ⟨Or.inl (hsame_refl compactMetricRead), compactMetricUnary⟩
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
          | inl sameCompact =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCompact)
          | inr rest =>
              cases rest with
              | inl sameVietoris =>
                  exact
                    Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameVietoris))
              | inr sameHausdorff =>
                  exact
                    Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameHausdorff))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompact =>
          right
          right
          right
          right
          right
          right
          right
          right
          left
          exact sameCompact
      | inr rest =>
          cases rest with
          | inl sameVietoris =>
              right
              right
              right
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
              right
              right
              right
              exact sameHausdorff
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, vietorisPkg, hausdorffPkg⟩
  }
  exact ⟨cert, compactMetricUnary, vietorisUnary, hausdorffUnary⟩

end BEDC.Derived.HyperspaceUp
