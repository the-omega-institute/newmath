import BEDC.Derived.NestedClosedBallUp

namespace BEDC.Derived.NestedClosedBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NestedClosedBallObligationPackage
    {M K F S R D E H C P N centerWindow readbackWindow dyadicSeal realSeal packageRead :
      BHist} :
    Cont F S centerWindow ->
      Cont centerWindow R readbackWindow ->
        Cont readbackWindow D dyadicSeal ->
          Cont dyadicSeal E realSeal ->
            Cont realSeal P packageRead ->
              UnaryHistory F ->
                UnaryHistory S ->
                  UnaryHistory R ->
                    UnaryHistory D ->
                      UnaryHistory E ->
                        UnaryHistory P ->
                          UnaryHistory centerWindow ∧ UnaryHistory readbackWindow ∧
                            UnaryHistory dyadicSeal ∧ UnaryHistory realSeal ∧
                              UnaryHistory packageRead ∧ Cont F S centerWindow ∧
                                Cont centerWindow R readbackWindow ∧
                                  Cont readbackWindow D dyadicSeal ∧ Cont dyadicSeal E realSeal ∧
                                    Cont realSeal P packageRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro filterStreamRoute centerReadbackRoute readbackDyadicRoute dyadicRealRoute
    realPackageRoute filterUnary streamUnary readbackUnary dyadicUnary realUnary packageUnary
  have centerWindowUnary : UnaryHistory centerWindow :=
    unary_cont_closed filterUnary streamUnary filterStreamRoute
  have readbackWindowUnary : UnaryHistory readbackWindow :=
    unary_cont_closed centerWindowUnary readbackUnary centerReadbackRoute
  have dyadicSealUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed readbackWindowUnary dyadicUnary readbackDyadicRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicSealUnary realUnary dyadicRealRoute
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed realSealUnary packageUnary realPackageRoute
  exact
    ⟨centerWindowUnary, readbackWindowUnary, dyadicSealUnary, realSealUnary, packageReadUnary,
      filterStreamRoute, centerReadbackRoute, readbackDyadicRoute, dyadicRealRoute,
      realPackageRoute⟩

end BEDC.Derived.NestedClosedBallUp
