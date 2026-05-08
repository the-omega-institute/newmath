import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AffineSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def AffineSpaceHistoryTorsorCarrier (point translation : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory translation

theorem AffineSpaceHistoryTorsorCarrier_append_translation
    {point translation action : BHist} :
    AffineSpaceHistoryTorsorCarrier point translation ->
      Cont point translation action ->
        AffineSpaceHistoryTorsorCarrier action translation ∧
          hsame action (append point translation) := by
  intro carrier actionCont
  have actionUnary : UnaryHistory action :=
    unary_cont_closed carrier.left carrier.right actionCont
  exact And.intro (And.intro actionUnary carrier.right) actionCont

theorem AffineSpaceHistoryTorsorCarrier_vector_action_stability
    {point point' translation translation' action action' : BHist} :
    AffineSpaceHistoryTorsorCarrier point translation ->
      AffineSpaceHistoryTorsorCarrier point' translation' ->
        hsame point point' -> hsame translation translation' ->
          Cont point translation action -> Cont point' translation' action' ->
            AffineSpaceHistoryTorsorCarrier action translation ∧
              AffineSpaceHistoryTorsorCarrier action' translation' ∧ hsame action action' := by
  intro carrier carrier' samePoint sameTranslation actionCont actionCont'
  have actionUnary : UnaryHistory action :=
    unary_cont_closed carrier.left carrier.right actionCont
  have actionUnary' : UnaryHistory action' :=
    unary_cont_closed carrier'.left carrier'.right actionCont'
  have sameAction : hsame action action' :=
    cont_respects_hsame samePoint sameTranslation actionCont actionCont'
  exact And.intro (And.intro actionUnary carrier.right)
    (And.intro (And.intro actionUnary' carrier'.right) sameAction)

end BEDC.Derived.AffineSpaceUp
