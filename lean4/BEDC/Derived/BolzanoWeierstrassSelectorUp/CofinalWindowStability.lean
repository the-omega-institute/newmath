import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSelectorCofinalWindowStability
    {B M Q W D R E H C P N cofinalWindow dyadicRead regularRead realSeal : BHist} :
    Cont B M W ->
      Cont W Q cofinalWindow ->
        Cont cofinalWindow D dyadicRead ->
          Cont dyadicRead R regularRead ->
            Cont regularRead E realSeal ->
              UnaryHistory B ->
                UnaryHistory M ->
                  UnaryHistory Q ->
                    UnaryHistory D ->
                      UnaryHistory R ->
                        UnaryHistory E ->
                          UnaryHistory W ∧ UnaryHistory cofinalWindow ∧
                            UnaryHistory dyadicRead ∧ UnaryHistory regularRead ∧
                              UnaryHistory realSeal ∧ hsame H H ∧ Cont B M W ∧
                                Cont W Q cofinalWindow ∧
                                  Cont cofinalWindow D dyadicRead ∧
                                    Cont dyadicRead R regularRead ∧
                                      Cont regularRead E realSeal ∧
                                        bolzanoWeierstrassSelectorFields
                                            (BolzanoWeierstrassSelectorUp.mk B M Q W D R E H
                                              C P N) =
                                          [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro selectedRoute cofinalRoute dyadicRoute regularRoute sealRoute bUnary mUnary qUnary
    dUnary rUnary eUnary
  have windowUnary : UnaryHistory W :=
    unary_cont_closed bUnary mUnary selectedRoute
  have cofinalUnary : UnaryHistory cofinalWindow :=
    unary_cont_closed windowUnary qUnary cofinalRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed cofinalUnary dUnary dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary rUnary regularRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularUnary eUnary sealRoute
  exact
    ⟨windowUnary, cofinalUnary, dyadicUnary, regularUnary, sealUnary, hsame_refl H,
      selectedRoute, cofinalRoute, dyadicRoute, regularRoute, sealRoute, rfl⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
