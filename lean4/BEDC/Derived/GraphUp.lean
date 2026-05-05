import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary

namespace BEDC.Derived.GraphUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def GraphEdge (h k g : BHist) : Prop :=
  UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g

def GraphEdgeClassifier (h k g h' k' g' : BHist) : Prop :=
  hsame h h' ∧ hsame k k' ∧ hsame g g'

theorem GraphEdge_classifier_transport {h k g h' k' g' : BHist} :
    GraphEdge h k g -> hsame h h' -> hsame k k' -> hsame g g' ->
      GraphEdge h' k' g' ∧ GraphEdgeClassifier h k g h' k' g' ∧
        UnaryHistory h' ∧ UnaryHistory k' ∧ Cont h' k' g' := by
  intro edge sameH sameK sameG
  have unaryH' : UnaryHistory h' := unary_transport edge.left sameH
  have unaryK' : UnaryHistory k' := unary_transport edge.right.left sameK
  have cont' : Cont h' k' g' :=
    cont_hsame_transport sameH sameK sameG edge.right.right
  exact And.intro
    (And.intro unaryH' (And.intro unaryK' cont'))
    (And.intro
      (And.intro sameH (And.intro sameK sameG))
      (And.intro unaryH' (And.intro unaryK' cont')))

def GraphContEdge (h k g : BHist) : Prop :=
  UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g

theorem GraphContEdge_classifier_transport {h k g h' k' g' : BHist} :
    GraphContEdge h k g -> hsame h h' -> hsame k k' -> hsame g g' ->
      GraphContEdge h' k' g' ∧ Cont h' k' g' ∧
        (hsame h h' ∧ hsame k k' ∧ hsame g g') := by
  intro edge sameH sameK sameG
  cases edge with
  | intro unaryH rest =>
      cases rest with
      | intro unaryK continuation =>
          have unaryH' : UnaryHistory h' := unary_transport unaryH sameH
          have unaryK' : UnaryHistory k' := unary_transport unaryK sameK
          have continuation' : Cont h' k' g' := by
            cases sameH
            cases sameK
            exact cont_result_hsame_transport continuation sameG
          exact And.intro (And.intro unaryH' (And.intro unaryK' continuation'))
            (And.intro continuation'
              (And.intro sameH (And.intro sameK sameG)))

end BEDC.Derived.GraphUp
