import BEDC.Derived.SeparatedMetricReflectionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SeparatedMetricReflectionCarrier_zero_distance_exactness
    {X S A U Z zeroRead adjunctionRead universalRead : BHist} :
    Cont X S zeroRead ->
      Cont zeroRead A adjunctionRead ->
        Cont adjunctionRead U universalRead ->
          UnaryHistory X ->
            UnaryHistory S ->
              UnaryHistory A ->
                UnaryHistory U ->
                  hsame Z Z /\ UnaryHistory zeroRead /\ UnaryHistory adjunctionRead /\
                    UnaryHistory universalRead /\ Cont X S zeroRead /\
                      Cont zeroRead A adjunctionRead /\ Cont adjunctionRead U universalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro zeroRoute adjunctionRoute universalRoute xUnary sUnary aUnary uUnary
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed xUnary sUnary zeroRoute
  have adjunctionUnary : UnaryHistory adjunctionRead :=
    unary_cont_closed zeroUnary aUnary adjunctionRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed adjunctionUnary uUnary universalRoute
  exact
    ⟨hsame_refl Z, zeroUnary, adjunctionUnary, universalUnary, zeroRoute,
      adjunctionRoute, universalRoute⟩

end BEDC.Derived.SeparatedMetricReflectionUp
