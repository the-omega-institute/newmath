import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSelectorNestedIntervalObligation
    {B M Q W D nested retained R E H C P N selectedWindow dyadicRead nestedRead regularRead
      sealRead : BHist} :
    Cont B M selectedWindow →
      Cont selectedWindow Q W →
        Cont W D dyadicRead →
          Cont dyadicRead nested nestedRead →
            Cont nestedRead retained regularRead →
              Cont regularRead E sealRead →
                UnaryHistory B →
                  UnaryHistory M →
                    UnaryHistory Q →
                      UnaryHistory D →
                        UnaryHistory nested →
                          UnaryHistory retained →
                            UnaryHistory E →
                              UnaryHistory selectedWindow ∧ UnaryHistory W ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory nestedRead ∧
                                  UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                                    Cont W D dyadicRead ∧
                                      Cont dyadicRead nested nestedRead ∧
                                        Cont nestedRead retained regularRead ∧
                                          Cont regularRead E sealRead ∧
                                            bolzanoWeierstrassSelectorFields
                                                (BolzanoWeierstrassSelectorUp.mk
                                                  B M Q W D R E H C P N) =
                                              [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro boundedSelected selectedCofinal dyadicRoute nestedRoute retainedRoute sealRoute
    boundedUnary monotoneUnary cofinalUnary dyadicUnary nestedUnary retainedUnary sealUnary
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed boundedUnary monotoneUnary boundedSelected
  have windowUnary : UnaryHistory W :=
    unary_cont_closed selectedUnary cofinalUnary selectedCofinal
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dyadicUnary dyadicRoute
  have nestedReadUnary : UnaryHistory nestedRead :=
    unary_cont_closed dyadicReadUnary nestedUnary nestedRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed nestedReadUnary retainedUnary retainedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary sealUnary sealRoute
  exact
    ⟨selectedUnary, windowUnary, dyadicReadUnary, nestedReadUnary, regularReadUnary,
      sealReadUnary, dyadicRoute, nestedRoute, retainedRoute, sealRoute, rfl⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
