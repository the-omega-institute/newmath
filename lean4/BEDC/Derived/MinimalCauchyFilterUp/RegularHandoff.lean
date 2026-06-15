import BEDC.Derived.MinimalCauchyFilterUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.MinimalCauchyFilterUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MinimalCauchyFilterCarrier_regular_handoff
    {F S R T D E H C P N supportRead scheduleRead toleranceRead regularRead : BHist} :
    UnaryHistory F -> UnaryHistory S -> UnaryHistory T -> UnaryHistory D -> UnaryHistory R ->
      Cont F S supportRead -> Cont supportRead T scheduleRead ->
        Cont scheduleRead D toleranceRead -> Cont toleranceRead R regularRead ->
          minimalCauchyFilterFromEventFlow
              (minimalCauchyFilterToEventFlow
                (MinimalCauchyFilterUp.mk F S R T D E H C P N)) =
            some (MinimalCauchyFilterUp.mk F S R T D E H C P N) ∧
            UnaryHistory supportRead ∧ UnaryHistory scheduleRead ∧
            UnaryHistory toleranceRead ∧ UnaryHistory regularRead ∧ Cont F S supportRead ∧
            Cont supportRead T scheduleRead ∧ Cont scheduleRead D toleranceRead ∧
            Cont toleranceRead R regularRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro filterUnary supportUnary scheduleUnary dyadicUnary regularUnary supportRoute scheduleRoute
    toleranceRoute regularRoute
  have roundTrip :
      minimalCauchyFilterFromEventFlow
          (minimalCauchyFilterToEventFlow
            (MinimalCauchyFilterUp.mk F S R T D E H C P N)) =
        some (MinimalCauchyFilterUp.mk F S R T D E H C P N) :=
    MinimalCauchyFilterUpTasteGate_single_carrier_alignment.right.left
      (MinimalCauchyFilterUp.mk F S R T D E H C P N)
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed filterUnary supportUnary supportRoute
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed supportReadUnary scheduleUnary scheduleRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed scheduleReadUnary dyadicUnary toleranceRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceReadUnary regularUnary regularRoute
  exact ⟨roundTrip, supportReadUnary, scheduleReadUnary, toleranceReadUnary, regularReadUnary,
    supportRoute, scheduleRoute, toleranceRoute, regularRoute⟩

theorem MinimalCauchyFilterCarrier_nonescape
    {F S R T D E H C P N supportRead scheduleRead toleranceRead regularRead
      sealRead : BHist} :
    UnaryHistory F → UnaryHistory S → UnaryHistory T → UnaryHistory D → UnaryHistory R →
      UnaryHistory E → Cont F S supportRead → Cont supportRead T scheduleRead →
        Cont scheduleRead D toleranceRead → Cont toleranceRead R regularRead →
          Cont regularRead E sealRead →
            UnaryHistory supportRead ∧ UnaryHistory scheduleRead ∧
              UnaryHistory toleranceRead ∧ UnaryHistory regularRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro filterUnary supportUnary scheduleUnary dyadicUnary regularUnary realUnary supportRoute
    scheduleRoute toleranceRoute regularRoute sealRoute
  have _roundTrip :
      minimalCauchyFilterFromEventFlow
          (minimalCauchyFilterToEventFlow
            (MinimalCauchyFilterUp.mk F S R T D E H C P N)) =
        some (MinimalCauchyFilterUp.mk F S R T D E H C P N) :=
    MinimalCauchyFilterUpTasteGate_single_carrier_alignment.right.left
      (MinimalCauchyFilterUp.mk F S R T D E H C P N)
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed filterUnary supportUnary supportRoute
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed supportReadUnary scheduleUnary scheduleRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed scheduleReadUnary dyadicUnary toleranceRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceReadUnary regularUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary realUnary sealRoute
  exact ⟨supportReadUnary, scheduleReadUnary, toleranceReadUnary, regularReadUnary, sealUnary⟩

end BEDC.Derived.MinimalCauchyFilterUp.TasteGate
