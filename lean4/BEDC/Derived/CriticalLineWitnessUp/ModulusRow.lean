import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_row
    {Z S M R Q H C P N request answer : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      UnaryHistory request ->
        Cont M request answer ->
          UnaryHistory M ∧ UnaryHistory answer ∧ hsame H (append Z S) ∧
            Cont M R Q := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet requestUnary answerRoute
  obtain ⟨_unaryZ, _unaryS, unaryM, _unaryR, _unaryP, sameH, routeQ, _routeC,
      _routeN⟩ := packet
  have answerUnary : UnaryHistory answer :=
    unary_cont_closed unaryM requestUnary answerRoute
  exact ⟨unaryM, answerUnary, sameH, routeQ⟩

end BEDC.Derived.CriticalLineWitnessUp
