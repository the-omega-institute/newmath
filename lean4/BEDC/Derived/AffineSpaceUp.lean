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

def AffineSpaceTranslationClassifier
    (point target left right leftAction rightAction : BHist) : Prop :=
  AffineSpaceHistoryTorsorCarrier point left ∧
    AffineSpaceHistoryTorsorCarrier point right ∧
      Cont point left leftAction ∧ Cont point right rightAction ∧
        hsame leftAction target ∧ hsame rightAction target

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

theorem AffineSpaceTranslationClassifier_witnesses_identified
    {point target left right leftAction rightAction : BHist} :
    AffineSpaceTranslationClassifier point target left right leftAction rightAction ->
      hsame left right ∧ AffineSpaceHistoryTorsorCarrier point left ∧
        AffineSpaceHistoryTorsorCarrier point right ∧ Cont point left leftAction ∧
          Cont point right rightAction ∧ hsame leftAction rightAction := by
  intro classifier
  have leftCont : Cont point left leftAction :=
    classifier.right.right.left
  have rightCont : Cont point right rightAction :=
    classifier.right.right.right.left
  have sameActions : hsame leftAction rightAction :=
    hsame_trans classifier.right.right.right.right.left
      (hsame_symm classifier.right.right.right.right.right)
  have rightContAtLeftAction : Cont point right leftAction :=
    cont_result_hsame_transport rightCont (hsame_symm sameActions)
  have sameTranslations : hsame left right :=
    cont_left_cancel leftCont rightContAtLeftAction
  exact And.intro sameTranslations
    (And.intro classifier.left
      (And.intro classifier.right.left
        (And.intro leftCont
          (And.intro rightCont sameActions))))

end BEDC.Derived.AffineSpaceUp
