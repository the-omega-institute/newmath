import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessCarrier_typing_exactness_route
    {T S B F R H C P N typingRead sameRead boundedRead finishedRead : BHist} :
    UnaryHistory T →
      UnaryHistory S →
        UnaryHistory B →
          UnaryHistory F →
            hsame H (append T S) →
              Cont T S typingRead →
                Cont typingRead S sameRead →
                  Cont sameRead B boundedRead →
                    Cont boundedRead F finishedRead →
                      Cont C P N →
                        UnaryHistory typingRead ∧
                          UnaryHistory sameRead ∧
                            UnaryHistory boundedRead ∧
                              UnaryHistory finishedRead ∧
                                hsame H (append T S) ∧
                                  Cont T S typingRead ∧
                                    Cont typingRead S sameRead ∧
                                      Cont sameRead B boundedRead ∧
                                        Cont boundedRead F finishedRead ∧
                                          Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory append
  intro hT hS hB hF hH hTyping hSame hBounded hFinished hRoute
  have typingUnary : UnaryHistory typingRead :=
    unary_cont_closed hT hS hTyping
  have sameUnary : UnaryHistory sameRead :=
    unary_cont_closed typingUnary hS hSame
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed sameUnary hB hBounded
  have finishedUnary : UnaryHistory finishedRead :=
    unary_cont_closed boundedUnary hF hFinished
  exact
    ⟨typingUnary, sameUnary, boundedUnary, finishedUnary, hH, hTyping, hSame,
      hBounded, hFinished, hRoute⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
