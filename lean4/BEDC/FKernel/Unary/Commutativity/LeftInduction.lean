import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem unary_append_comm_hsame_left_induction :
    forall {h k : BHist}, UnaryHistory h -> UnaryHistory k ->
      hsame (append h k) (append k h) := by
  intro h k uh uk
  induction h generalizing k with
  | Empty =>
      exact append_empty_left k
  | e0 _ _ =>
      cases uh
  | e1 h ih =>
      exact (unary_append_e1_left (h := k) (k := h) uk).trans (hsame_e1_congr (ih uh uk))

theorem unary_append_comm_hsame_left_induction_closed_pair :
    forall {h k : BHist}, UnaryHistory h -> UnaryHistory k ->
      hsame (append h k) (append k h) ∧
        UnaryHistory (append h k) ∧ UnaryHistory (append k h) := by
  intro h k uh uk
  constructor
  · exact unary_append_comm_hsame_left_induction uh uk
  · constructor
    · exact unary_append_closed uh uk
    · exact unary_append_closed uk uh

end BEDC.FKernel.Unary
