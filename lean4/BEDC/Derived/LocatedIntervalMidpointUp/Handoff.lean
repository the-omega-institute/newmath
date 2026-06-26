import BEDC.Derived.LocatedIntervalMidpointUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedIntervalMidpointUp.Handoff

open BEDC.Derived.LocatedIntervalMidpointUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LocatedIntervalMidpointCarrier_refinement_handoff
    {I D E0 E1 B S R Q H C P N parentRead midpointRead bisectionRead sealedRead :
      BHist} :
    UnaryHistory I ->
      UnaryHistory D ->
        UnaryHistory E0 ->
          UnaryHistory B ->
            UnaryHistory Q ->
              Cont I D parentRead ->
                Cont parentRead E0 midpointRead ->
                  Cont midpointRead B bisectionRead ->
                    Cont bisectionRead Q sealedRead ->
                      locatedIntervalMidpointFromEventFlow
                          (locatedIntervalMidpointToEventFlow
                            (LocatedIntervalMidpointUp.mk I D E0 E1 B S R Q H C P N)) =
                        some (LocatedIntervalMidpointUp.mk I D E0 E1 B S R Q H C P N) ∧
                        UnaryHistory parentRead ∧ UnaryHistory midpointRead ∧
                          UnaryHistory bisectionRead ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: LocatedIntervalMidpointUp BHist Cont UnaryHistory BMark
  intro iUnary dUnary e0Unary bUnary qUnary parentRoute midpointRoute bisectionRoute sealRoute
  have parentUnary : UnaryHistory parentRead :=
    unary_cont_closed iUnary dUnary parentRoute
  have midpointUnary : UnaryHistory midpointRead :=
    unary_cont_closed parentUnary e0Unary midpointRoute
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed midpointUnary bUnary bisectionRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed bisectionUnary qUnary sealRoute
  exact
    ⟨locatedIntervalMidpointChapterTasteGate.round_trip
        (LocatedIntervalMidpointUp.mk I D E0 E1 B S R Q H C P N),
      parentUnary, midpointUnary, bisectionUnary, sealedUnary⟩

end BEDC.Derived.LocatedIntervalMidpointUp.Handoff
