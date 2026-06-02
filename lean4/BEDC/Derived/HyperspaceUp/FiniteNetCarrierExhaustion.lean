import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Hyperspace_finite_net_carrier_exhaustion [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead finiteNetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 K1 subsetRead ->
        Cont N0 N1 netRead ->
          Cont subsetRead netRead finiteNetRead ->
            PkgSig bundle finiteNetRead pkg ->
              UnaryHistory X ∧ UnaryHistory K0 ∧ UnaryHistory K1 ∧
                UnaryHistory N0 ∧ UnaryHistory N1 ∧ UnaryHistory subsetRead ∧
                  UnaryHistory netRead ∧ UnaryHistory finiteNetRead ∧
                    Cont subsetRead netRead finiteNetRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle finiteNetRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier subsetRoute netRoute finiteNetRoute finiteNetPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed subsetUnary netUnary finiteNetRoute
  exact
    ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, subsetUnary, netUnary,
      finiteNetUnary, finiteNetRoute, provenancePkg, finiteNetPkg⟩

end BEDC.Derived.HyperspaceUp
