import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem unaryCont_comm_and_results_closed {h k r r' : BHist} :
    UnaryCont h k r -> UnaryCont k h r' -> UnaryHistory r /\ UnaryHistory r' /\ hsame r r' := by
  intro hcont khcont
  cases hcont with
  | intro uh hrest =>
      cases hrest with
      | intro uk hr =>
          cases khcont with
          | intro _ khrest =>
              cases khrest with
              | intro _ hr' =>
                  constructor
                  · exact unary_cont_closed uh uk hr
                  · constructor
                    · exact unary_cont_closed uk uh hr'
                    · exact unary_cont_comm uh uk hr hr'

theorem unaryCont_comm_sameness_pair {h k r r' : BHist} :
    UnaryCont h k r -> UnaryCont k h r' -> hsame r r' /\ hsame r' r := by
  intro hcont khcont
  cases hcont with
  | intro uh hrest =>
      cases hrest with
      | intro uk hr =>
          cases khcont with
          | intro _ khrest =>
              cases khrest with
              | intro _ hr' =>
                  have same : hsame r r' := unary_cont_comm uh uk hr hr'
                  exact ⟨same, hsame_symm same⟩

end BEDC.FKernel.Unary
