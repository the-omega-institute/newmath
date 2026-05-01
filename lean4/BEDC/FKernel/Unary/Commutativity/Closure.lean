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

theorem unary_cont_comm_symmetric_pair {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' ->
      hsame r r' /\ hsame r' r := by
  intro uh uk hr hr'
  have same : hsame r r' := unary_cont_comm uh uk hr hr'
  exact ⟨same, hsame_symm same⟩

theorem unaryCont_comm_closed_symmetric_pair {h k r r' : BHist} :
    UnaryCont h k r -> UnaryCont k h r' ->
      UnaryHistory r /\ UnaryHistory r' /\ hsame r r' /\ hsame r' r := by
  intro hcont khcont
  have closed := unaryCont_comm_and_results_closed hcont khcont
  have same := unaryCont_comm_sameness_pair hcont khcont
  constructor
  · exact closed.left
  · constructor
    · exact closed.right.left
    · exact same

end BEDC.FKernel.Unary
