import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSelectorFiniteNestedWindowInduction
    {B M Q W D R E H C P N selectedWindow dyadicRead nestedRead retainedWindow regularRead
      sealRead clusterRead : BHist} :
    Cont B M selectedWindow →
      Cont selectedWindow Q W →
        Cont W D dyadicRead →
          Cont dyadicRead Q nestedRead →
            Cont nestedRead D retainedWindow →
              Cont retainedWindow R regularRead →
                Cont regularRead E sealRead →
                  Cont sealRead C clusterRead →
                    UnaryHistory B →
                      UnaryHistory M →
                        UnaryHistory Q →
                          UnaryHistory D →
                            UnaryHistory R →
                              UnaryHistory E →
                                UnaryHistory C →
                                  UnaryHistory selectedWindow ∧ UnaryHistory W ∧
                                    UnaryHistory dyadicRead ∧ UnaryHistory nestedRead ∧
                                      UnaryHistory retainedWindow ∧ UnaryHistory regularRead ∧
                                        UnaryHistory sealRead ∧ UnaryHistory clusterRead ∧
                                          Cont W D dyadicRead ∧
                                            Cont dyadicRead Q nestedRead ∧
                                              Cont nestedRead D retainedWindow ∧
                                                Cont retainedWindow R regularRead ∧
                                                  Cont regularRead E sealRead ∧
                                                    Cont sealRead C clusterRead ∧
                                                      bolzanoWeierstrassSelectorFields
                                                          (BolzanoWeierstrassSelectorUp.mk B M Q W
                                                            D R E H C P N) =
                                                        [B, M, Q, W, D, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute windowRoute dyadicRoute nestedRoute retainedRoute regularRoute sealRoute
    clusterRoute bUnary mUnary qUnary dUnary rUnary eUnary cUnary
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed bUnary mUnary selectedRoute
  have windowUnary : UnaryHistory W :=
    unary_cont_closed selectedUnary qUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed dyadicUnary qUnary nestedRoute
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed nestedUnary dUnary retainedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed retainedUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed sealUnary cUnary clusterRoute
  exact
    ⟨selectedUnary, windowUnary, dyadicUnary, nestedUnary, retainedUnary, regularUnary, sealUnary,
      clusterUnary, dyadicRoute, nestedRoute, retainedRoute, regularRoute, sealRoute,
      clusterRoute, rfl⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
