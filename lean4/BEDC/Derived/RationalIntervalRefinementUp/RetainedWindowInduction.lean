import BEDC.Derived.RationalIntervalRefinementUp

namespace BEDC.Derived.RationalIntervalRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalRefinementRetainedWindowInduction [AskSetup] [PackageSetup]
    {I0 J0 E0 W0 K0 H0 C0 P0 N0 I1 J1 E1 W1 K1 H1 C1 P1 N1
      retained : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier I0 J0 E0 W0 K0 H0 C0 P0 N0 bundle pkg →
      RationalIntervalRefinementCarrier I1 J1 E1 W1 K1 H1 C1 P1 N1 bundle pkg →
        hsame J0 I1 →
          Cont W0 W1 retained →
            UnaryHistory retained ∧
              Cont I0 J0 E0 ∧
                Cont E0 W0 K0 ∧
                  Cont K0 H0 C0 ∧
                    Cont I1 J1 E1 ∧
                      Cont E1 W1 K1 ∧
                        Cont K1 H1 C1 ∧
                          hsame J0 I1 ∧
                            PkgSig bundle P0 pkg ∧ PkgSig bundle N1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier0 carrier1 bridge retainedRoute
  obtain ⟨_i0Unary, _j0Unary, _e0Unary, w0Unary, _k0Unary, _h0Unary, _c0Unary,
    _p0Unary, _n0Unary, routeI0J0, routeE0W0, routeK0H0, pkgP0, _pkgN0⟩ := carrier0
  obtain ⟨_i1Unary, _j1Unary, _e1Unary, w1Unary, _k1Unary, _h1Unary, _c1Unary,
    _p1Unary, _n1Unary, routeI1J1, routeE1W1, routeK1H1, _pkgP1, pkgN1⟩ := carrier1
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed w0Unary w1Unary retainedRoute
  exact
    ⟨retainedUnary, routeI0J0, routeE0W0, routeK0H0, routeI1J1, routeE1W1,
      routeK1H1, bridge, pkgP0, pkgN1⟩

end BEDC.Derived.RationalIntervalRefinementUp
