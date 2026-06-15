import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Mark

theorem BolzanoWeierstrassSelectorWindowObligation
    {B M Q W D R E H C P N selectedWindow dyadicRead regularRead realSeal : BHist} :
    Cont B M selectedWindow ->
      Cont selectedWindow Q W ->
        Cont W D dyadicRead ->
          Cont dyadicRead R regularRead ->
            Cont regularRead E realSeal ->
              UnaryHistory B ->
                UnaryHistory M ->
                  UnaryHistory Q ->
                    UnaryHistory D ->
                      UnaryHistory R ->
                        UnaryHistory E ->
                          UnaryHistory selectedWindow ∧
                            UnaryHistory W ∧
                              UnaryHistory dyadicRead ∧
                                UnaryHistory regularRead ∧
                                  UnaryHistory realSeal ∧
                                    Cont B M selectedWindow ∧
                                      Cont selectedWindow Q W ∧
                                        Cont W D dyadicRead ∧
                                          Cont dyadicRead R regularRead ∧
                                            Cont regularRead E realSeal ∧
                                              bolzanoWeierstrassSelectorFields
                                                  (BolzanoWeierstrassSelectorUp.mk
                                                    B M Q W D R E H C P N) =
                                                [B, M, Q, W, D, R, E, H, C, P, N] ∧
                                                bolzanoWeierstrassSelectorEncodeBHist
                                                    BHist.Empty =
                                                  ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro hBM hQ hD hR hE uB uM uQ uD uR uE
  have uSelectedWindow : UnaryHistory selectedWindow :=
    unary_cont_closed uB uM hBM
  have uW : UnaryHistory W :=
    unary_cont_closed uSelectedWindow uQ hQ
  have uDyadicRead : UnaryHistory dyadicRead :=
    unary_cont_closed uW uD hD
  have uRegularRead : UnaryHistory regularRead :=
    unary_cont_closed uDyadicRead uR hR
  have uRealSeal : UnaryHistory realSeal :=
    unary_cont_closed uRegularRead uE hE
  exact
    ⟨uSelectedWindow, uW, uDyadicRead, uRegularRead, uRealSeal, hBM, hQ, hD, hR,
      hE, rfl, rfl⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
