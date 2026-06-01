import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceHitMissCoverageTotality [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M hit miss vietoris publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont D0 D1 hit ->
        Cont K0 K1 miss ->
          Cont hit miss vietoris ->
            Cont vietoris R publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory hit ∧ UnaryHistory miss ∧ UnaryHistory vietoris ∧
                  UnaryHistory publicRead ∧ Cont D0 D1 hit ∧ Cont K0 K1 miss ∧
                    Cont hit miss vietoris ∧ Cont vietoris R publicRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier hitRoute missRoute vietorisRoute publicRoute publicPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary, rUnary,
    _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have hitUnary : UnaryHistory hit :=
    unary_cont_closed d0Unary d1Unary hitRoute
  have missUnary : UnaryHistory miss :=
    unary_cont_closed k0Unary k1Unary missRoute
  have vietorisUnary : UnaryHistory vietoris :=
    unary_cont_closed hitUnary missUnary vietorisRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed vietorisUnary rUnary publicRoute
  exact
    ⟨hitUnary, missUnary, vietorisUnary, publicUnary, hitRoute, missRoute,
      vietorisRoute, publicRoute, provenancePkg, publicPkg⟩

end BEDC.Derived.HyperspaceUp
