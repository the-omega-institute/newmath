import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AffineSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def AffineSpaceHistoryTorsorCarrier (point translation : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory translation

def AffineSpaceTranslationClassifier
    (point target left right leftAction rightAction : BHist) : Prop :=
  AffineSpaceHistoryTorsorCarrier point left ∧
    AffineSpaceHistoryTorsorCarrier point right ∧
      Cont point left leftAction ∧ Cont point right rightAction ∧
        hsame leftAction target ∧ hsame rightAction target

theorem AffineSpaceTranslationClassifier_separation_obligation
    {point target identityAction : BHist} :
    UnaryHistory point ->
      Cont point BHist.Empty identityAction ->
        hsame identityAction target ->
          AffineSpaceTranslationClassifier point target BHist.Empty BHist.Empty identityAction
            identityAction := by
  intro pointUnary identityCont sameTarget
  exact
    And.intro (And.intro pointUnary unary_empty)
      (And.intro (And.intro pointUnary unary_empty)
        (And.intro identityCont
          (And.intro identityCont
            (And.intro sameTarget sameTarget))))

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

theorem AffineSpaceHistoryTorsorCarrier_action_closure_obligation
    {point translation action target : BHist} :
    AffineSpaceHistoryTorsorCarrier point translation ->
      Cont point translation action ->
        hsame action target ->
          AffineSpaceHistoryTorsorCarrier action translation ∧
            AffineSpaceHistoryTorsorCarrier target translation ∧ hsame action target := by
  intro carrier actionCont sameActionTarget
  have actionCarrier :
      AffineSpaceHistoryTorsorCarrier action translation :=
    (AffineSpaceHistoryTorsorCarrier_append_translation carrier actionCont).left
  have targetCarrier : AffineSpaceHistoryTorsorCarrier target translation :=
    And.intro (unary_transport actionCarrier.left sameActionTarget) actionCarrier.right
  exact And.intro actionCarrier
    (And.intro targetCarrier sameActionTarget)

theorem AffineSpaceTranslationClassifier_action_coverage_obligation
    {point target translation action : BHist} :
    AffineSpaceHistoryTorsorCarrier point translation ->
      Cont point translation action ->
        hsame action target ->
          ∃ endpoint : BHist,
            AffineSpaceHistoryTorsorCarrier endpoint translation ∧
              AffineSpaceTranslationClassifier point target translation translation action action ∧
                hsame endpoint target := by
  intro carrier actionCont sameActionTarget
  have closure :=
    AffineSpaceHistoryTorsorCarrier_action_closure_obligation carrier actionCont sameActionTarget
  exact Exists.intro action
    (And.intro closure.left
      (And.intro
        (And.intro carrier
          (And.intro carrier
            (And.intro actionCont
              (And.intro actionCont
                (And.intro sameActionTarget sameActionTarget)))))
        sameActionTarget))

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

theorem AffineSpaceHistoryTorsorCarrier_action_additivity
    {point first second combined direct iterated firstEndpoint : BHist} :
    AffineSpaceHistoryTorsorCarrier point first ->
      UnaryHistory second ->
        Cont first second combined ->
          Cont point combined direct ->
            Cont point first firstEndpoint ->
              Cont firstEndpoint second iterated ->
                hsame direct iterated ∧
                  AffineSpaceHistoryTorsorCarrier direct combined ∧
                    AffineSpaceHistoryTorsorCarrier iterated second := by
  intro carrier secondUnary combinedCont directCont firstCont iteratedCont
  have combinedUnary : UnaryHistory combined :=
    unary_cont_closed carrier.right secondUnary combinedCont
  have directUnary : UnaryHistory direct :=
    unary_cont_closed carrier.left combinedUnary directCont
  have firstEndpointUnary : UnaryHistory firstEndpoint :=
    unary_cont_closed carrier.left carrier.right firstCont
  have iteratedUnary : UnaryHistory iterated :=
    unary_cont_closed firstEndpointUnary secondUnary iteratedCont
  have sameIteratedDirect : hsame iterated direct :=
    cont_assoc_hsame firstCont iteratedCont combinedCont directCont
  exact
    And.intro (hsame_symm sameIteratedDirect)
      (And.intro (And.intro directUnary combinedUnary)
        (And.intro iteratedUnary secondUnary))

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

theorem AffineSpaceTranslationClassifier_free_action_obligation
    {point left right leftAction rightAction : BHist} :
    AffineSpaceHistoryTorsorCarrier point left ->
        AffineSpaceHistoryTorsorCarrier point right ->
          Cont point left leftAction ->
            Cont point right rightAction ->
            hsame leftAction rightAction -> hsame left right := by
  intro _leftCarrier _rightCarrier leftCont rightCont sameActions
  have rightContAtLeftAction : Cont point right leftAction :=
    cont_result_hsame_transport rightCont (hsame_symm sameActions)
  exact cont_left_cancel leftCont rightContAtLeftAction

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

theorem AffineSpaceHistoryTorsorCarrier_action_coverage_obligation
    {point target translation action : BHist} :
    AffineSpaceHistoryTorsorCarrier point translation ->
      Cont point translation action ->
        hsame action target ->
          ∃ vector endpoint : BHist, AffineSpaceHistoryTorsorCarrier point vector ∧
            Cont point vector endpoint ∧ hsame endpoint target ∧
              AffineSpaceTranslationClassifier point target vector translation endpoint action := by
  intro carrier actionCont sameActionTarget
  exact
    Exists.intro translation
      (Exists.intro action
        (And.intro carrier
          (And.intro actionCont
            (And.intro sameActionTarget
              (And.intro carrier
                (And.intro carrier
                  (And.intro actionCont
                    (And.intro actionCont
                      (And.intro sameActionTarget sameActionTarget)))))))))

theorem AffineSpaceHistoryTorsorCarrier_semantic_name_certificate {point translation : BHist} :
    AffineSpaceHistoryTorsorCarrier point translation ->
      SemanticNameCert
        (fun p : BHist => AffineSpaceHistoryTorsorCarrier p translation)
        (fun p : BHist => AffineSpaceHistoryTorsorCarrier p translation)
        (fun p : BHist => AffineSpaceHistoryTorsorCarrier p translation)
        (fun p q : BHist =>
          AffineSpaceHistoryTorsorCarrier p translation ∧
            AffineSpaceHistoryTorsorCarrier q translation ∧ hsame p q) := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro point carrier
      equiv_refl := by
        intro p pCarrier
        exact And.intro pCarrier (And.intro pCarrier (hsame_refl p))
      equiv_symm := by
        intro _p _q classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro _p _q _r classifiedPQ classifiedQR
        exact And.intro classifiedPQ.left
          (And.intro classifiedQR.right.left
            (hsame_trans classifiedPQ.right.right classifiedQR.right.right))
      carrier_respects_equiv := by
        intro _p _q classified _pCarrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _p pCarrier
      exact pCarrier
    ledger_sound := by
      intro _p pCarrier
      exact pCarrier
  }

theorem AffineSpaceTranslationClassifier_ledger_exactness
    {point target left right leftAction rightAction : BHist} :
    AffineSpaceTranslationClassifier point target left right leftAction rightAction ->
      AffineSpaceHistoryTorsorCarrier point left ∧
        AffineSpaceHistoryTorsorCarrier point right ∧
          Cont point left leftAction ∧ Cont point right rightAction ∧
            hsame leftAction target ∧ hsame rightAction target ∧ hsame left right ∧
              hsame leftAction rightAction := by
  intro classifier
  have witnesses :=
    AffineSpaceTranslationClassifier_witnesses_identified classifier
  exact And.intro classifier.left
    (And.intro classifier.right.left
      (And.intro classifier.right.right.left
          (And.intro classifier.right.right.right.left
            (And.intro classifier.right.right.right.right.left
              (And.intro classifier.right.right.right.right.right
                (And.intro witnesses.left witnesses.right.right.right.right.right))))))

end BEDC.Derived.AffineSpaceUp
