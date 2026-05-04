import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary

namespace BEDC.Derived.AddUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem AddUnaryContinuation_hsame_transport {h h' k k' r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> hsame h h' -> hsame k k' ->
      hsame r r' -> UnaryHistory h' ∧ UnaryHistory k' ∧ UnaryHistory r' ∧ Cont h' k' r' := by
  intro unaryH unaryK continuation sameH sameK sameR
  have unaryH' : UnaryHistory h' := unary_transport unaryH sameH
  have unaryK' : UnaryHistory k' := unary_transport unaryK sameK
  have continuation' : Cont h' k' r' :=
    cont_hsame_transport sameH sameK sameR continuation
  have unaryR' : UnaryHistory r' := unary_cont_closed unaryH' unaryK' continuation'
  exact ⟨unaryH', unaryK', unaryR', continuation'⟩

end BEDC.Derived.AddUp
