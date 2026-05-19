import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_comparison_ledger
    {Z S M R Q H C P N comparisonRead replayRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R comparisonRead →
        Cont comparisonRead H replayRead →
          hsame comparisonRead Q ∧ UnaryHistory comparisonRead ∧
            UnaryHistory replayRead ∧ hsame H (append Z S) ∧
              Cont M R comparisonRead ∧ Cont comparisonRead H replayRead ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet comparisonRoute replayRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, routeN⟩ :=
    packet
  have comparisonSame : hsame comparisonRead Q :=
    cont_deterministic comparisonRoute routeQ
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed comparisonUnary unaryH replayRoute
  exact
    ⟨comparisonSame, comparisonUnary, replayUnary, sameH, comparisonRoute, replayRoute,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
