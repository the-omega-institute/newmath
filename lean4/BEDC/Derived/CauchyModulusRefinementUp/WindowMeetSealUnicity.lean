import BEDC.Derived.CauchyModulusRefinementUp

/-!
# CauchyModulusRefinementUp window-meet seal unicity.
-/

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_window_meet_seal_unicity
    [AskSetup] [PackageSetup]
    {m0 m1 u v0 v1 t w q e0 e1 h0 h1 c0 c1 p0 p1 n0 n1 public0 public1 :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v0 t w q e0 h0 c0 p0 n0 bundle pkg ->
      CauchyModulusRefinementCarrier m0 m1 u v1 t w q e1 h1 c1 p1 n1 bundle pkg ->
        hsame e0 e1 ->
          hsame h0 h1 ->
            Cont e0 h0 public0 ->
              Cont e1 h1 public1 ->
                PkgSig bundle public0 pkg ->
                  PkgSig bundle public1 pkg ->
                    hsame public0 public1 ∧ UnaryHistory public0 ∧
                      UnaryHistory public1 ∧ Cont m0 m1 u ∧ Cont u v0 t ∧
                        Cont u v1 t ∧ Cont t w q ∧ Cont q e0 h0 ∧
                          Cont q e1 h1 ∧ Cont e0 h0 public0 ∧
                            Cont e1 h1 public1 ∧ PkgSig bundle public0 pkg ∧
                              PkgSig bundle public1 pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier0 carrier1 sameSeal sameHandoff publicRoute0 publicRoute1 publicPkg0 publicPkg1
  rcases carrier0 with
    ⟨_m0Unary, _m1Unary, _uUnary, v0Unary, _tUnary, _wUnary, _qUnary, e0Unary,
      h0Unary, _c0Unary, _p0Unary, _n0Unary, m0m1u, uv0t, twq, qe0h0, _p0Pkg,
      _h0n0⟩
  rcases carrier1 with
    ⟨_m0Unary1, _m1Unary1, _uUnary1, _v1Unary, _tUnary1, _wUnary1, _qUnary1,
      _e1Unary, _h1Unary, _c1Unary, _p1Unary, _n1Unary, _m0m1u1, uv1t, _twq1,
      qe1h1, _p1Pkg, _h1n1⟩
  have samePublic : hsame public0 public1 :=
    cont_respects_hsame sameSeal sameHandoff publicRoute0 publicRoute1
  have public0Unary : UnaryHistory public0 :=
    unary_cont_closed e0Unary h0Unary publicRoute0
  have public1Unary : UnaryHistory public1 :=
    unary_transport public0Unary samePublic
  exact
    ⟨samePublic, public0Unary, public1Unary, m0m1u, uv0t, uv1t, twq, qe0h0, qe1h1,
      publicRoute0, publicRoute1, publicPkg0, publicPkg1⟩

end BEDC.Derived.CauchyModulusRefinementUp
