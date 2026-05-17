import BEDC.FKernel.Unary
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealCompletionWitnessExtractorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def RealCompletionWitnessExtractorCarrier (D W M Q L S _H C P N : BHist) : Prop :=
  UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory S ∧
    Cont D W Q ∧ Cont Q M L ∧ Cont L S C ∧ hsame N (append P C)

theorem RealCompletionWitnessExtractorCarrier_selected_window_admission
    {D W M Q L S H C P N : BHist} :
    RealCompletionWitnessExtractorCarrier D W M Q L S H C P N ->
      UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory C ∧ Cont D W Q ∧
          Cont Q M L ∧ Cont L S C ∧ hsame N (append P C) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro carrier
  obtain ⟨unaryD, unaryW, unaryM, unaryS, routeQ, routeL, routeC, nameSame⟩ := carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryD unaryW routeQ
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryQ unaryM routeL
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryL unaryS routeC
  exact
    ⟨unaryD, unaryW, unaryM, unaryQ, unaryL, unaryS, unaryC, routeQ, routeL,
      routeC, nameSame⟩

end BEDC.Derived.RealCompletionWitnessExtractorUp
