import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementSharedWindowCompletionSealCoherence [AskSetup] [PackageSetup]
    {m0 m1 u v0 v1 v2 t w q e0 e1 e2 h0 h1 h2 c0 c1 c2 p0 p1 p2 n0 n1 n2
      b s d r selectorSeal public01 public12 public02 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v0 t w q e0 h0 c0 p0 n0 bundle pkg ->
      CauchyModulusRefinementCarrier m0 m1 u v1 t w q e1 h1 c1 p1 n1 bundle pkg ->
        CauchyModulusRefinementCarrier m0 m1 u v2 t w q e2 h2 c2 p2 n2 bundle pkg ->
          hsame e0 e1 ->
            hsame e1 e2 ->
              Cont e0 e1 public01 ->
                Cont e1 e2 public12 ->
                  Cont e0 e2 public02 ->
                    UnaryHistory b ->
                      UnaryHistory s ->
                        UnaryHistory d ->
                          Cont b s w ->
                            Cont w d r ->
                              Cont r e2 selectorSeal ->
                                PkgSig bundle selectorSeal pkg ->
                                  hsame e0 e2 ∧ UnaryHistory public01 ∧
                                    UnaryHistory public12 ∧ UnaryHistory public02 ∧
                                      UnaryHistory r ∧ UnaryHistory selectorSeal ∧
                                        Cont e0 e1 public01 ∧ Cont e1 e2 public12 ∧
                                          Cont e0 e2 public02 ∧ Cont b s w ∧
                                            Cont w d r ∧ Cont r e2 selectorSeal ∧
                                              PkgSig bundle p2 pkg ∧
                                                PkgSig bundle selectorSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier0 carrier1 carrier2 same01 same12 publicRoute01 publicRoute12 publicRoute02
    bUnary sUnary dUnary bsw wdr selectorSealRoute selectorSealPkg
  rcases carrier0 with
    ⟨_m0Unary0, _m1Unary0, _uUnary0, _v0Unary, _tUnary0, _wUnary0, _qUnary0, e0Unary,
      _h0Unary, _c0Unary, _p0Unary, _n0Unary, _m0m1u0, _uv0t, _twq0, _qe0h0,
      _p0Pkg, _h0n0⟩
  rcases carrier1 with
    ⟨_m0Unary1, _m1Unary1, _uUnary1, _v1Unary, _tUnary1, _wUnary1, _qUnary1, e1Unary,
      _h1Unary, _c1Unary, _p1Unary, _n1Unary, _m0m1u1, _uv1t, _twq1, _qe1h1,
      _p1Pkg, _h1n1⟩
  rcases carrier2 with
    ⟨_m0Unary2, _m1Unary2, _uUnary2, _v2Unary, _tUnary2, _wUnary2, _qUnary2, e2Unary,
      _h2Unary, _c2Unary, p2Unary, _n2Unary, _m0m1u2, _uv2t, _twq2, _qe2h2,
      p2Pkg, _h2n2⟩
  have same02 : hsame e0 e2 :=
    hsame_trans same01 same12
  have public01Unary : UnaryHistory public01 :=
    unary_cont_closed e0Unary e1Unary publicRoute01
  have public12Unary : UnaryHistory public12 :=
    unary_cont_closed e1Unary e2Unary publicRoute12
  have public02Unary : UnaryHistory public02 :=
    unary_cont_closed e0Unary e2Unary publicRoute02
  have _wUnary : UnaryHistory w :=
    unary_cont_closed bUnary sUnary bsw
  have rUnary : UnaryHistory r :=
    unary_cont_closed _wUnary dUnary wdr
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed rUnary e2Unary selectorSealRoute
  exact
    ⟨same02, public01Unary, public12Unary, public02Unary, rUnary, selectorSealUnary,
      publicRoute01, publicRoute12, publicRoute02, bsw, wdr, selectorSealRoute, p2Pkg,
      selectorSealPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
