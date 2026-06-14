import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_p11961_modulus_ledger_separation
    {Z S M R Q H C P N zeroRoute comparisonRoute : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRoute ->
        Cont M R comparisonRoute ->
          UnaryHistory zeroRoute ∧ UnaryHistory comparisonRoute ∧
            hsame H (append Z S) ∧ Cont Z S zeroRoute ∧ Cont M R comparisonRoute ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zeroRouteCont comparisonRouteCont
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryZeroRoute : UnaryHistory zeroRoute :=
    unary_cont_closed unaryZ unaryS zeroRouteCont
  have unaryComparisonRoute : UnaryHistory comparisonRoute :=
    unary_cont_closed unaryM unaryR comparisonRouteCont
  exact
    ⟨unaryZeroRoute, unaryComparisonRoute, sameH, zeroRouteCont,
      comparisonRouteCont, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
