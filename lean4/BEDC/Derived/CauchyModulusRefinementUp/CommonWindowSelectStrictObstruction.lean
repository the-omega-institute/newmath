import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_common_window_select_strict_obstruction
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w q ->
        Cont q e h ->
          Cont h c refusalRead ->
            PkgSig bundle refusalRead pkg ->
              UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory h ∧
                UnaryHistory refusalRead ∧ Cont t w q ∧ Cont q e h ∧
                  Cont h c refusalRead ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier windowRoute sealRoute refusalRoute refusalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, _qUnary, eUnary,
      hUnary, cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have qUnary : UnaryHistory q :=
    unary_cont_closed tUnary wUnary windowRoute
  have hUnaryFromSeal : UnaryHistory h :=
    unary_cont_closed qUnary eUnary sealRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed hUnary cUnary refusalRoute
  exact
    ⟨wUnary, qUnary, eUnary, hUnaryFromSeal, refusalUnary, windowRoute, sealRoute,
      refusalRoute, pPkg, refusalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
