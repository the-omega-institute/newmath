import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChoiceSequenceRealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ChoiceSequenceRealCarrier_finite_prefix_regularity
    {F S R D E H T P N prefixRead regularRead sealRead transportRead : BHist} :
    UnaryHistory F →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory D →
            UnaryHistory E →
              UnaryHistory H →
                UnaryHistory P →
                  Cont F S prefixRead →
                    Cont prefixRead R regularRead →
                      Cont D E sealRead →
                        Cont regularRead H transportRead →
                          Cont transportRead P N →
                            UnaryHistory prefixRead ∧ UnaryHistory regularRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory transportRead ∧
                                UnaryHistory N ∧ Cont F S prefixRead ∧
                                  Cont prefixRead R regularRead ∧ Cont D E sealRead ∧
                                    Cont regularRead H transportRead ∧
                                      Cont transportRead P N := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fUnary sUnary rUnary dUnary eUnary hUnary pUnary prefixRoute regularRoute
    sealRoute transportRoute endpointRoute
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed fUnary sUnary prefixRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed prefixUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dUnary eUnary sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed regularUnary hUnary transportRoute
  have endpointUnary : UnaryHistory N :=
    unary_cont_closed transportUnary pUnary endpointRoute
  exact
    ⟨prefixUnary, regularUnary, sealUnary, transportUnary, endpointUnary, prefixRoute,
      regularRoute, sealRoute, transportRoute, endpointRoute⟩

end BEDC.Derived.ChoiceSequenceRealUp
