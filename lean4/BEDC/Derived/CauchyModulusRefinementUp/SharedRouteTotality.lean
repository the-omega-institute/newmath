import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_shared_route_totality [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n publicA publicB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c publicA ->
        Cont h c publicB ->
          PkgSig bundle publicA pkg ->
            PkgSig bundle publicB pkg ->
              UnaryHistory publicA ∧ UnaryHistory publicB ∧ Cont m0 m1 u ∧ Cont u v t ∧
                Cont t w q ∧ Cont q e h ∧ Cont h c publicA ∧ Cont h c publicB ∧
                  hsame publicA publicB ∧ PkgSig bundle publicA pkg ∧
                    PkgSig bundle publicB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier hCPublicA hCPublicB publicAPkg publicBPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      hUnary, cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, qeh, _pPkg, _hn⟩
  have publicAUnary : UnaryHistory publicA :=
    unary_cont_closed hUnary cUnary hCPublicA
  have publicBUnary : UnaryHistory publicB :=
    unary_cont_closed hUnary cUnary hCPublicB
  have publicSame : hsame publicA publicB :=
    cont_respects_hsame (hsame_refl h) (hsame_refl c) hCPublicA hCPublicB
  exact
    ⟨publicAUnary, publicBUnary, m0m1u, uvt, twq, qeh, hCPublicA, hCPublicB,
      publicSame, publicAPkg, publicBPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
