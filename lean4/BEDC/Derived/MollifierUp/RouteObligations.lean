import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.MollifierUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MollifierCarrier_support_normalization_obligation
    {S R N P C H L supportRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          Cont S R N →
            Cont N P supportRead →
              UnaryHistory N ∧ UnaryHistory supportRead ∧
                Cont S R N ∧ Cont N P supportRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary rUnary pUnary supportRoute readRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed nUnary pUnary readRoute
  exact ⟨nUnary, supportReadUnary, supportRoute, readRoute⟩

theorem MollifierCarrier_convolution_window_obligation
    {S R N P C H L replayRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            Cont S R N →
              Cont N P C →
                Cont C H replayRead →
                  UnaryHistory N ∧ UnaryHistory C ∧ UnaryHistory replayRead ∧
                    Cont S R N ∧ Cont N P C ∧ Cont C H replayRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary rUnary pUnary hUnary supportRoute convolutionRoute replayRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed nUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed cUnary hUnary replayRoute
  exact ⟨nUnary, cUnary, replayUnary, supportRoute, convolutionRoute, replayRoute⟩

end BEDC.Derived.MollifierUp
