import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.GraphUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem GraphContNameCert_surface :
    SemanticNameCert UnaryHistory UnaryHistory UnaryHistory
        (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) ∧
      (forall {h k g : BHist}, (UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g) ->
        UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g) ∧
      (forall {h k g h' k' g' : BHist},
        (UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g) ->
          hsame h h' ∧ hsame k k' ∧ hsame g g' ->
            UnaryHistory h' ∧ UnaryHistory k' ∧ Cont h' k' g') := by
  have semantic :
      SemanticNameCert UnaryHistory UnaryHistory UnaryHistory
        (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty unary_empty
      equiv_refl := by
        intro h unaryH
        exact And.intro unaryH (And.intro unaryH (hsame_refl h))
      equiv_symm := by
        intro h k same
        exact And.intro same.right.left (And.intro same.left (hsame_symm same.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k same _unaryH
        exact same.right.left
    }
    pattern_sound := by
      intro h unaryH
      exact unaryH
    ledger_sound := by
      intro h unaryH
      exact unaryH
  }
  have edgeReadback :
      forall {h k g : BHist}, (UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g) ->
        UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g := by
    intro h k g edge
    exact edge
  have edgeTransport :
      forall {h k g h' k' g' : BHist},
        (UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g) ->
          hsame h h' ∧ hsame k k' ∧ hsame g g' ->
            UnaryHistory h' ∧ UnaryHistory k' ∧ Cont h' k' g' := by
    intro h k g h' k' g' edge same
    have unaryH' : UnaryHistory h' :=
      unary_transport edge.left same.left
    have unaryK' : UnaryHistory k' :=
      unary_transport edge.right.left same.right.left
    have cont' : Cont h' k' g' :=
      cont_hsame_transport same.left same.right.left same.right.right edge.right.right
    exact And.intro unaryH' (And.intro unaryK' cont')
  exact And.intro semantic (And.intro edgeReadback edgeTransport)

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
          have continuation' : Cont h' k' g' :=
            cont_hsame_transport sameH sameK sameG continuation
          exact And.intro (And.intro unaryH' (And.intro unaryK' continuation'))
            (And.intro continuation'
              (And.intro sameH (And.intro sameK sameG)))

end BEDC.Derived.GraphUp
