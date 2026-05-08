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

def AffineSpaceTranslationClassifier
    (point point' vector vector' action action' : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory point' ∧ UnaryHistory vector ∧ UnaryHistory vector' ∧
    Cont point vector action ∧ Cont point' vector' action' ∧ hsame action action'

theorem AffineSpaceTranslationClassifier_hsame_transport
    {point point' vector vector' action action' pointT pointT' vectorT vectorT'
      actionT actionT' : BHist} :
    AffineSpaceTranslationClassifier point point' vector vector' action action' ->
      hsame point pointT ->
        hsame point' pointT' ->
          hsame vector vectorT ->
            hsame vector' vectorT' ->
              Cont pointT vectorT actionT ->
                Cont pointT' vectorT' actionT' ->
                  AffineSpaceTranslationClassifier pointT pointT' vectorT vectorT' actionT actionT' ∧
                    hsame action actionT ∧ hsame action' actionT' := by
  intro classifier samePoint samePoint' sameVector sameVector' actionTCont actionT'Cont
  have pointTUnary : UnaryHistory pointT :=
    unary_transport classifier.left samePoint
  have pointT'Unary : UnaryHistory pointT' :=
    unary_transport classifier.right.left samePoint'
  have vectorTUnary : UnaryHistory vectorT :=
    unary_transport classifier.right.right.left sameVector
  have vectorT'Unary : UnaryHistory vectorT' :=
    unary_transport classifier.right.right.right.left sameVector'
  have sameActionT : hsame action actionT :=
    cont_respects_hsame samePoint sameVector classifier.right.right.right.right.left actionTCont
  have sameActionT' : hsame action' actionT' :=
    cont_respects_hsame samePoint' sameVector'
      classifier.right.right.right.right.right.left actionT'Cont
  have sameTransportedActions : hsame actionT actionT' :=
    hsame_trans (hsame_symm sameActionT)
      (hsame_trans classifier.right.right.right.right.right.right sameActionT')
  constructor
  · exact
      And.intro pointTUnary
        (And.intro pointT'Unary
          (And.intro vectorTUnary
            (And.intro vectorT'Unary
              (And.intro actionTCont
                (And.intro actionT'Cont sameTransportedActions)))))
  · exact And.intro sameActionT sameActionT'

end BEDC.Derived.AffineSpaceUp
