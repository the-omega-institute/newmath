import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.GraphUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

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

theorem GraphCont_namecert_surface :
    SemanticNameCert UnaryHistory UnaryHistory UnaryHistory hsame ∧
      (forall {h k g : BHist}, GraphContEdge h k g ->
        UnaryHistory h ∧ UnaryHistory k ∧ Cont h k g) ∧
        (forall {h k g h' k' g' : BHist}, GraphContEdge h k g -> hsame h h' ->
          hsame k k' -> hsame g g' -> GraphContEdge h' k' g') := by
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have vertexCert : SemanticNameCert UnaryHistory UnaryHistory UnaryHistory hsame := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyUnary
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same carrier
        exact unary_transport carrier same
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }
  exact And.intro vertexCert
    (And.intro
      (by
        intro h k g edge
        exact edge)
      (by
        intro h k g h' k' g' edge sameH sameK sameG
        exact (GraphContEdge_classifier_transport edge sameH sameK sameG).left))

end BEDC.Derived.GraphUp
