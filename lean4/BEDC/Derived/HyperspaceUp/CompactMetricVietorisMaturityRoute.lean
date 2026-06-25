import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceMatureCompactMetricVietorisRoute [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactMetricRead vietorisRead bridgeRead
      hausdorffRead kuratowskiRead compactSubsetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont X K0 compactMetricRead ->
        Cont compactMetricRead N0 vietorisRead ->
          Cont vietorisRead P bridgeRead ->
            Cont D0 D1 hausdorffRead ->
              Cont K1 R kuratowskiRead ->
                Cont bridgeRead kuratowskiRead compactSubsetRead ->
                  PkgSig bundle compactSubsetRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row compactSubsetRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row compactMetricRead ∨ hsame row vietorisRead ∨
                            hsame row bridgeRead ∨ hsame row hausdorffRead ∨
                              hsame row kuratowskiRead ∨ hsame row compactSubsetRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont X K0 compactMetricRead ∧
                            Cont compactMetricRead N0 vietorisRead ∧
                              Cont vietorisRead P bridgeRead ∧
                                Cont D0 D1 hausdorffRead ∧ Cont K1 R kuratowskiRead ∧
                                  Cont bridgeRead kuratowskiRead compactSubsetRead ∧
                                    PkgSig bundle P pkg ∧
                                      PkgSig bundle compactSubsetRead pkg)
                        hsame ∧ UnaryHistory compactSubsetRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist ProbeBundle Pkg Cont SemanticNameCert
  intro carrier compactMetricRoute vietorisRoute bridgeRoute hausdorffRoute
    kuratowskiRoute compactSubsetRoute compactSubsetPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, pUnary, _mUnary, provenancePkg⟩ := carrier
  have compactMetricUnary : UnaryHistory compactMetricRead :=
    unary_cont_closed xUnary k0Unary compactMetricRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed compactMetricUnary n0Unary vietorisRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed vietorisUnary pUnary bridgeRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed d0Unary d1Unary hausdorffRoute
  have kuratowskiUnary : UnaryHistory kuratowskiRead :=
    unary_cont_closed k1Unary rUnary kuratowskiRoute
  have compactSubsetUnary : UnaryHistory compactSubsetRead :=
    unary_cont_closed bridgeUnary kuratowskiUnary compactSubsetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactSubsetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetricRead ∨ hsame row vietorisRead ∨
              hsame row bridgeRead ∨ hsame row hausdorffRead ∨
                hsame row kuratowskiRead ∨ hsame row compactSubsetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X K0 compactMetricRead ∧
              Cont compactMetricRead N0 vietorisRead ∧ Cont vietorisRead P bridgeRead ∧
                Cont D0 D1 hausdorffRead ∧ Cont K1 R kuratowskiRead ∧
                  Cont bridgeRead kuratowskiRead compactSubsetRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle compactSubsetRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compactSubsetRead
          ⟨hsame_refl compactSubsetRead, compactSubsetUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactMetricRoute, vietorisRoute, bridgeRoute, hausdorffRoute,
          kuratowskiRoute, compactSubsetRoute, provenancePkg, compactSubsetPkg⟩
  }
  exact ⟨cert, compactSubsetUnary⟩

end BEDC.Derived.HyperspaceUp
