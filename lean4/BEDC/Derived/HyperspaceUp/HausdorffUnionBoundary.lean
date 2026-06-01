import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceHausdorffUnionBoundary [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M leftDistance rightDistance unionDistance
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont D0 R leftDistance ->
        Cont D1 R rightDistance ->
          Cont leftDistance rightDistance unionDistance ->
            Cont unionDistance Hs publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory leftDistance ∧ UnaryHistory rightDistance ∧
                  UnaryHistory unionDistance ∧ UnaryHistory publicRead ∧
                    Cont leftDistance rightDistance unionDistance ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                            hsame row Hs ∨ hsame row leftDistance ∨
                              hsame row rightDistance ∨ hsame row unionDistance ∨
                                hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle publicRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier leftRoute rightRoute unionRoute publicRoute publicPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have leftUnary : UnaryHistory leftDistance :=
    unary_cont_closed d0Unary rUnary leftRoute
  have rightUnary : UnaryHistory rightDistance :=
    unary_cont_closed d1Unary rUnary rightRoute
  have unionUnary : UnaryHistory unionDistance :=
    unary_cont_closed leftUnary rightUnary unionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unionUnary hsUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨ hsame row Hs ∨
              hsame row leftDistance ∨ hsame row rightDistance ∨
                hsame row unionDistance ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, publicPkg⟩
  }
  exact ⟨leftUnary, rightUnary, unionUnary, publicUnary, unionRoute, cert⟩

end BEDC.Derived.HyperspaceUp
