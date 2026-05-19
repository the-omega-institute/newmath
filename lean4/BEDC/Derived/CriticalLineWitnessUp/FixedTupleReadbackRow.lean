import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_tuple_readback_row
    {Z S M R Q H C P N image readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q image ->
        Cont image H readback ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory image ∧ UnaryHistory readback ∧ hsame H (append Z S) ∧
              Cont (append Z S) Q image ∧ Cont image H readback := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet imageRoute readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have imageUnary : UnaryHistory image :=
    unary_cont_closed sourceUnary unaryQ imageRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed imageUnary unaryH readbackRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryH, imageUnary, readbackUnary, sameH, imageRoute,
      readbackRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
