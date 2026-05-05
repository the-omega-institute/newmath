import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Cont.Units
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

theorem GraphContEdge_row_inversion :
    (forall {h h' k g : BHist}, GraphContEdge h k g -> GraphContEdge h' k g ->
      Cont h k g ∧ Cont h' k g ∧ hsame h h') ∧
    (forall {h k k' g : BHist}, GraphContEdge h k g -> GraphContEdge h k' g ->
      Cont h k g ∧ Cont h k' g ∧ hsame k k') ∧
    (forall {h k g g' : BHist}, GraphContEdge h k g -> GraphContEdge h k g' ->
      Cont h k g ∧ Cont h k g' ∧ hsame g g') := by
  constructor
  · intro h h' k g left right
    exact And.intro left.right.right
      (And.intro right.right.right (cont_right_cancel left.right.right right.right.right))
  constructor
  · intro h k k' g left right
    exact And.intro left.right.right
      (And.intro right.right.right (cont_left_cancel left.right.right right.right.right))
  · intro h k g g' left right
    exact And.intro left.right.right
      (And.intro right.right.right (cont_deterministic left.right.right right.right.right))

theorem GraphContEdge_unit_loop {h gL gR : BHist} :
    UnaryHistory h -> GraphContEdge BHist.Empty h h ∧ GraphContEdge h BHist.Empty h ∧
      (GraphContEdge BHist.Empty h gL -> hsame gL h) ∧
        (GraphContEdge h BHist.Empty gR -> hsame gR h) := by
  intro unaryH
  exact And.intro
    (And.intro unary_empty (And.intro unaryH (cont_left_unit h)))
    (And.intro
      (And.intro unaryH (And.intro unary_empty (cont_right_unit h)))
      (And.intro
        (by
          intro edge
          exact cont_left_unit_result edge.right.right)
        (by
          intro edge
          exact cont_right_unit_result edge.right.right)))

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

theorem GraphContEdge_two_step_composition {h k l hk kl : BHist} :
    GraphContEdge h k hk -> GraphContEdge k l kl ->
      exists left : BHist, exists right : BHist,
        GraphContEdge hk l left ∧ GraphContEdge h kl right ∧ hsame left right := by
  intro hkEdge klEdge
  have hkUnary : UnaryHistory hk :=
    unary_cont_closed hkEdge.left hkEdge.right.left hkEdge.right.right
  have klUnary : UnaryHistory kl :=
    unary_cont_closed klEdge.left klEdge.right.left klEdge.right.right
  cases cont_assoc_exists_hsame hkEdge.right.right klEdge.right.right with
  | intro left leftData =>
      cases leftData with
      | intro right data =>
          exact Exists.intro left
            (Exists.intro right
              (And.intro
                (And.intro hkUnary (And.intro klEdge.right.left data.left))
                  (And.intro
                    (And.intro hkEdge.left (And.intro klUnary data.right.left))
                    data.right.right)))

theorem GraphContEdge_composition_closure {h k l hk kl : BHist} :
    GraphContEdge h k hk -> GraphContEdge k l kl ->
      exists left : BHist, exists right : BHist,
        GraphContEdge hk l left ∧ GraphContEdge h kl right ∧ Cont hk l left ∧
          Cont h kl right ∧ hsame left right := by
  intro edgeHK edgeKL
  have unaryHK : UnaryHistory hk :=
    unary_cont_closed edgeHK.left edgeHK.right.left edgeHK.right.right
  have unaryKL : UnaryHistory kl :=
    unary_cont_closed edgeKL.left edgeKL.right.left edgeKL.right.right
  let left : BHist := append hk l
  let right : BHist := append h kl
  have contLeft : Cont hk l left := cont_intro rfl
  have contRight : Cont h kl right := cont_intro rfl
  have sameLR : hsame left right :=
    cont_assoc_hsame edgeHK.right.right contLeft edgeKL.right.right contRight
  exact Exists.intro left
    (Exists.intro right
      (And.intro (And.intro unaryHK (And.intro edgeKL.right.left contLeft))
        (And.intro (And.intro edgeHK.left (And.intro unaryKL contRight))
          (And.intro contLeft (And.intro contRight sameLR)))))

theorem GraphContEdge_visible_tail_step_closure {h k g : BHist} :
    GraphContEdge h k g -> UnaryHistory (BHist.e0 k) -> UnaryHistory (BHist.e0 g) ->
      UnaryHistory (BHist.e1 k) -> UnaryHistory (BHist.e1 g) ->
        GraphContEdge h (BHist.e0 k) (BHist.e0 g) ∧
          GraphContEdge h (BHist.e1 k) (BHist.e1 g) := by
  intro edge unaryKZero unaryGZero unaryKOne unaryGOne
  have zeroStep : Cont h (BHist.e0 k) (BHist.e0 g) :=
    cont_step_zero edge.right.right
  have oneStep : Cont h (BHist.e1 k) (BHist.e1 g) :=
    cont_step_one edge.right.right
  exact And.intro
    (And.intro edge.left (And.intro unaryKZero zeroStep))
    (And.intro edge.left (And.intro unaryKOne oneStep))

end BEDC.Derived.GraphUp
