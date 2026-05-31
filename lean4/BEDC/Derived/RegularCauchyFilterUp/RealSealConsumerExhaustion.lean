import BEDC.Derived.RegularCauchyFilterUp

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFilterCarrier_real_seal_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {B R T D M E H C P N windowRead basisRead regReadback realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont T D windowRead ->
                Cont windowRead M basisRead ->
                  Cont basisRead R regReadback ->
                    Cont regReadback E realSealRead ->
                      PkgSig bundle realSealRead pkg ->
                        regularCauchyFilterFromEventFlow
                            (regularCauchyFilterToEventFlow
                              (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
                          some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
                          UnaryHistory windowRead ∧ UnaryHistory basisRead ∧
                            UnaryHistory regReadback ∧ UnaryHistory realSealRead ∧
                              Cont T D windowRead ∧ Cont windowRead M basisRead ∧
                                Cont basisRead R regReadback ∧
                                  Cont regReadback E realSealRead ∧
                                    PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro tUnary dUnary mUnary rUnary eUnary windowRoute basisRoute regRoute sealRoute
    sealPkg
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have roundTrip :
      regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow
            (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) := by
    rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tUnary dUnary windowRoute
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed windowUnary mUnary basisRoute
  have readbackUnary : UnaryHistory regReadback :=
    unary_cont_closed basisUnary rUnary regRoute
  have sealUnary : UnaryHistory realSealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  exact
    ⟨roundTrip, windowUnary, basisUnary, readbackUnary, sealUnary, windowRoute,
      basisRoute, regRoute, sealRoute, sealPkg⟩

end BEDC.Derived.RegularCauchyFilterUp
