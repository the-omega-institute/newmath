import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCompactHausdorffDistanceRoute [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M leftCoverage rightCoverage hausdorffRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont D0 R leftCoverage ->
        Cont D1 R rightCoverage ->
          Cont leftCoverage rightCoverage hausdorffRead ->
            Cont Hs C replayRead ->
              PkgSig bundle hausdorffRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row hausdorffRead ∨ hsame row replayRead) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                        hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                          hsame row hausdorffRead ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle hausdorffRead pkg)
                    hsame ∧
                  UnaryHistory leftCoverage ∧ UnaryHistory rightCoverage ∧
                    UnaryHistory hausdorffRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier leftRoute rightRoute hausdorffRoute replayRoute hausdorffPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have leftUnary : UnaryHistory leftCoverage :=
    unary_cont_closed d0Unary rUnary leftRoute
  have rightUnary : UnaryHistory rightCoverage :=
    unary_cont_closed d1Unary rUnary rightRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed leftUnary rightUnary hausdorffRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row hausdorffRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row hausdorffRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle hausdorffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro hausdorffRead
          ⟨Or.inl (hsame_refl hausdorffRead), hausdorffUnary⟩
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
        intro row row' sameRows source
        cases source.left with
        | inl sameHausdorff =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameHausdorff),
                unary_transport source.right sameRows⟩
        | inr sameReplay =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameReplay),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      cases source.left with
      | inl sameHausdorff =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl sameHausdorff))))))))
      | inr sameReplay =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr sameReplay))))))))
    ledger_sound := by
      intro row source
      exact ⟨source.right, provenancePkg, hausdorffPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, hausdorffUnary, replayUnary⟩

end BEDC.Derived.HyperspaceUp
