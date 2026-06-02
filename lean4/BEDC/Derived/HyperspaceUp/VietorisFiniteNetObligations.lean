import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisFiniteNetObligations [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead vietorisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 K1 subsetRead ->
        Cont N0 N1 netRead ->
          Cont subsetRead netRead vietorisRead ->
            PkgSig bundle vietorisRead pkg ->
              UnaryHistory X ∧ UnaryHistory K0 ∧ UnaryHistory K1 ∧ UnaryHistory N0 ∧
                UnaryHistory N1 ∧ UnaryHistory D0 ∧ UnaryHistory D1 ∧
                  UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                    UnaryHistory vietorisRead ∧ Cont subsetRead netRead vietorisRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle vietorisRead pkg := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle PkgSig UnaryHistory
  intro carrier subsetRoute netRoute vietorisRoute vietorisPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed subsetUnary netUnary vietorisRoute
  exact
    ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, subsetUnary,
      netUnary, vietorisUnary, vietorisRoute, provenancePkg, vietorisPkg⟩

end BEDC.Derived.HyperspaceUp
