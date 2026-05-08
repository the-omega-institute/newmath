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

theorem AffineSpaceTranslationClassifier_classifier_transport
    {point target left right leftAction rightAction point' target' left' right' leftAction'
      rightAction' : BHist} :
    AffineSpaceTranslationClassifier point target left right leftAction rightAction ->
      hsame point point' ->
        hsame target target' ->
          hsame left left' ->
            hsame right right' ->
              Cont point' left' leftAction' ->
                Cont point' right' rightAction' ->
                  hsame leftAction' target' ->
                    hsame rightAction' target' ->
                      AffineSpaceTranslationClassifier point' target' left' right' leftAction'
                          rightAction' ∧
                        hsame leftAction leftAction' ∧ hsame rightAction rightAction' := by
  intro classifier samePoint sameTarget sameLeft sameRight leftCont' rightCont'
    sameLeftActionTarget' sameRightActionTarget'
  have pointUnary' : UnaryHistory point' :=
    unary_transport classifier.left.left samePoint
  have leftUnary' : UnaryHistory left' :=
    unary_transport classifier.left.right sameLeft
  have rightUnary' : UnaryHistory right' :=
    unary_transport classifier.right.left.right sameRight
  have sameLeftAction : hsame leftAction leftAction' :=
    cont_respects_hsame samePoint sameLeft classifier.right.right.left leftCont'
  have sameRightAction : hsame rightAction rightAction' :=
    cont_respects_hsame samePoint sameRight classifier.right.right.right.left rightCont'
  exact
    And.intro
      (And.intro (And.intro pointUnary' leftUnary')
        (And.intro (And.intro pointUnary' rightUnary')
          (And.intro leftCont'
            (And.intro rightCont'
              (And.intro sameLeftActionTarget' sameRightActionTarget')))))
      (And.intro sameLeftAction sameRightAction)

theorem AffineSpaceTranslationClassifier_transport
    {point point' target target' left left' right right' leftAction leftAction' rightAction
      rightAction' : BHist} :
    AffineSpaceTranslationClassifier point target left right leftAction rightAction ->
      hsame point point' ->
        hsame target target' ->
          hsame left left' ->
            hsame right right' ->
              Cont point' left' leftAction' ->
                Cont point' right' rightAction' ->
                  AffineSpaceTranslationClassifier point' target' left' right' leftAction'
                      rightAction' ∧
                    hsame leftAction leftAction' ∧ hsame rightAction rightAction' := by
  intro classifier samePoint sameTarget sameLeft sameRight leftActionCont rightActionCont
  have pointUnary : UnaryHistory point' :=
    unary_transport classifier.left.left samePoint
  have leftUnary : UnaryHistory left' :=
    unary_transport classifier.left.right sameLeft
  have rightUnary : UnaryHistory right' :=
    unary_transport classifier.right.left.right sameRight
  have sameLeftAction : hsame leftAction leftAction' :=
    cont_respects_hsame samePoint sameLeft classifier.right.right.left leftActionCont
  have sameRightAction : hsame rightAction rightAction' :=
    cont_respects_hsame samePoint sameRight classifier.right.right.right.left rightActionCont
  have leftTarget : hsame leftAction' target' :=
    hsame_trans (hsame_symm sameLeftAction)
      (hsame_trans classifier.right.right.right.right.left sameTarget)
  have rightTarget : hsame rightAction' target' :=
    hsame_trans (hsame_symm sameRightAction)
      (hsame_trans classifier.right.right.right.right.right sameTarget)
  constructor
  · exact
      And.intro (And.intro pointUnary leftUnary)
        (And.intro (And.intro pointUnary rightUnary)
          (And.intro leftActionCont
            (And.intro rightActionCont
              (And.intro leftTarget rightTarget))))
  · exact And.intro sameLeftAction sameRightAction

end BEDC.Derived.AffineSpaceUp
