import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.GraphUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def GraphContEdge (h k g : BHist) : Prop :=
  UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g

theorem GraphContEdge_classifier_transport {h k g h' k' g' : BHist} :
    GraphContEdge h k g -> hsame h h' -> hsame k k' -> hsame g g' ->
      GraphContEdge h' k' g' ∧ hsame h h' ∧ hsame k k' ∧ hsame g g' := by
  intro edge sameH sameK sameG
  cases edge with
  | intro unaryH rest =>
      cases rest with
      | intro unaryK row =>
          have unaryH' : UnaryHistory h' :=
            unary_transport unaryH sameH
          have unaryK' : UnaryHistory k' :=
            unary_transport unaryK sameK
          have row' : Cont h' k' g' :=
            cont_hsame_transport sameH sameK sameG row
          exact And.intro
            (And.intro unaryH' (And.intro unaryK' row'))
            (And.intro sameH (And.intro sameK sameG))

end BEDC.Derived.GraphUp
