import BEDC.Derived.SheafUp.ChartGluingTrace
import BEDC.Derived.SheafUp.ConsumerAccessTrace

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafSchemeChartGluingTrace_consumer_access_trace
    {point common : BHist} {sections : List BHist} {out : BHist} :
    SheafSchemeChartGluingTrace point common sections out ->
      SheafConsumerAccessTrace common sections ∧ UnaryHistory out := by
  intro trace
  induction trace with
  | nil _ commonUnary =>
      exact And.intro
        (And.intro commonUnary
          (by
            intro row rowMem
            cases rowMem))
        unary_empty
  | cons commonUnary sectionUnary commonSection _tailTrace germTail tailRows =>
      have germUnary : UnaryHistory _ :=
        unary_cont_closed commonUnary sectionUnary commonSection
      have outUnary : UnaryHistory _ :=
        unary_cont_closed germUnary tailRows.right germTail
      exact And.intro
        (And.intro commonUnary
          (by
            intro row rowMem
            cases rowMem with
            | head =>
                exact sectionUnary
            | tail _ tailMem =>
                exact tailRows.left.right row tailMem))
        outUnary

end BEDC.Derived.SheafUp
