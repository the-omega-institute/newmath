import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary

namespace BEDC.Derived.NatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def NatUnaryStrictPrefix (h k : BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧ (tail = BHist.Empty → False) ∧ Cont h tail k

theorem NatUnaryStrictPrefix_one_step {h : BHist} :
    UnaryHistory h -> NatUnaryStrictPrefix h (BHist.e1 h) := by
  intro _uh
  exact ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty,
    (fun empty => by cases empty), cont_intro rfl⟩

theorem NatUnaryStrictPrefix_asymm {h k : BHist} :
    NatUnaryStrictPrefix h k -> NatUnaryStrictPrefix k h -> False := by
  intro forward backward
  cases forward with
  | intro forwardTail forwardData =>
      cases forwardData with
      | intro _forwardUnary forwardStrictData =>
          cases forwardStrictData with
          | intro forwardNonempty forwardCont =>
              cases backward with
              | intro backwardTail backwardData =>
                  cases backwardData with
                  | intro _backwardUnary backwardStrictData =>
                      cases backwardStrictData with
                      | intro _backwardNonempty backwardCont =>
                          have same : hsame h k :=
                            cont_mutual_extension_hsame forwardCont backwardCont
                          have unitAtTarget : Cont h BHist.Empty k :=
                            cont_result_hsame_transport (cont_right_unit h) same
                          have forwardEmpty : forwardTail = BHist.Empty :=
                            cont_left_cancel forwardCont unitAtTarget
                          exact forwardNonempty forwardEmpty

theorem NatUnaryStrictPrefix_empty_right_absurd {h : BHist} :
    NatUnaryStrictPrefix h BHist.Empty -> False := by
  intro strict
  cases strict with
  | intro tail data =>
      have parts := cont_empty_result_inversion data.right.right
      exact data.right.left parts.right

theorem NatUnaryStrictPrefix_e1_inversion {h k : BHist} :
    NatUnaryStrictPrefix (BHist.e1 h) (BHist.e1 k) -> NatUnaryStrictPrefix h k := by
  intro strict
  cases strict with
  | intro tail data =>
      cases data with
      | intro tailUnary strictData =>
          cases strictData with
          | intro tailNonempty tailCont =>
              cases tail with
              | Empty =>
                  exact False.elim (tailNonempty rfl)
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension tailUnary)
              | e1 tail =>
                  have tailInnerUnary : UnaryHistory tail := unary_e1_inversion tailUnary
                  have tailStep :
                      append (BHist.e1 h) tail = BHist.e1 (append h tail) :=
                    unary_append_e1_left (h := tail) (k := h) tailInnerUnary
                  have loweredCont : Cont h (BHist.e1 tail) k := by
                    exact cont_intro ((BHist.e1.inj tailCont).trans tailStep)
                  exact ⟨BHist.e1 tail, tailUnary, (fun empty => by cases empty), loweredCont⟩

theorem NatUnaryStrictPrefix_append_tail_trans {h k l leftTail rightTail : BHist} :
    UnaryHistory leftTail -> (leftTail = BHist.Empty -> False) -> Cont h leftTail k ->
      UnaryHistory rightTail -> (rightTail = BHist.Empty -> False) -> Cont k rightTail l ->
        NatUnaryStrictPrefix h l ∧ Cont h (append leftTail rightTail) l := by
  intro leftUnary leftNonempty leftCont rightUnary _rightNonempty rightCont
  have joinedCont : Cont h (append leftTail rightTail) l := by
    cases leftCont
    cases rightCont
    exact cont_intro (append_assoc h leftTail rightTail)
  have joinedStrict : NatUnaryStrictPrefix h l := by
    exact ⟨append leftTail rightTail, unary_append_closed leftUnary rightUnary,
      (fun appendedEmpty => leftNonempty (append_eq_empty_iff.mp appendedEmpty).left), joinedCont⟩
  exact And.intro joinedStrict joinedCont

theorem NatUnaryStrictPrefix_trans_composite_tail {h k l : BHist} :
    NatUnaryStrictPrefix h k -> NatUnaryStrictPrefix k l ->
      exists tail : BHist,
        UnaryHistory tail ∧ (tail = BHist.Empty -> False) ∧ Cont h tail l ∧
          NatUnaryStrictPrefix h l := by
  intro leftStrict rightStrict
  cases leftStrict with
  | intro leftTail leftData =>
      cases leftData with
      | intro leftUnary leftRest =>
          cases leftRest with
          | intro leftNonempty leftCont =>
              cases rightStrict with
              | intro rightTail rightData =>
                  cases rightData with
                  | intro rightUnary rightRest =>
                      cases rightRest with
                      | intro rightNonempty rightCont =>
                          have joined :=
                            NatUnaryStrictPrefix_append_tail_trans leftUnary leftNonempty
                              leftCont rightUnary rightNonempty rightCont
                          exact Exists.intro (append leftTail rightTail)
                            (And.intro (unary_append_closed leftUnary rightUnary)
                              (And.intro
                                (fun appendedEmpty =>
                                  leftNonempty (append_eq_empty_iff.mp appendedEmpty).left)
                                (And.intro joined.right joined.left)))

theorem NatUnaryPrefix_total {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      (exists tail : BHist, UnaryHistory tail /\ Cont h tail k) \/
        (exists tail : BHist, UnaryHistory tail /\ Cont k tail h) := by
  intro uh uk
  induction h generalizing k with
  | Empty =>
      exact Or.inl ⟨k, uk, cont_left_unit k⟩
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      cases k with
      | Empty =>
          exact Or.inr ⟨BHist.e1 h, uh, cont_left_unit (BHist.e1 h)⟩
      | e0 k =>
          cases uk
      | e1 k =>
          have recResult := ih (k := k) uh uk
          cases recResult with
          | inl left =>
              cases left with
              | intro tail data =>
                  cases data with
                  | intro tailUnary tailCont =>
                      have base : Cont (BHist.e1 h) tail (BHist.e1 (append h tail)) := by
                        exact cont_intro
                          (unary_append_e1_left (h := tail) (k := h) tailUnary).symm
                      have same : hsame (BHist.e1 (append h tail)) (BHist.e1 k) := by
                        exact hsame_e1_congr tailCont.symm
                      exact Or.inl
                        ⟨tail, tailUnary, cont_result_hsame_transport base same⟩
          | inr right =>
              cases right with
              | intro tail data =>
                  cases data with
                  | intro tailUnary tailCont =>
                      have base : Cont (BHist.e1 k) tail (BHist.e1 (append k tail)) := by
                        exact cont_intro
                          (unary_append_e1_left (h := tail) (k := k) tailUnary).symm
                      have same : hsame (BHist.e1 (append k tail)) (BHist.e1 h) := by
                        exact hsame_e1_congr tailCont.symm
                      exact Or.inr
                        ⟨tail, tailUnary, cont_result_hsame_transport base same⟩

theorem NatUnaryPrefix_directed_common_upper {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      exists upper : BHist, And (UnaryHistory upper)
        (And (exists tail : BHist, And (UnaryHistory tail) (Cont h tail upper))
          (exists tail : BHist, And (UnaryHistory tail) (Cont k tail upper))) := by
  intro uh uk
  have total := NatUnaryPrefix_total uh uk
  cases total with
  | inl left =>
      cases left with
      | intro tail data =>
          cases data with
          | intro tailUnary tailCont =>
              exact Exists.intro k
                (And.intro uk
                  (And.intro
                    (Exists.intro tail (And.intro tailUnary tailCont))
                    (Exists.intro BHist.Empty
                      (And.intro unary_empty (cont_right_unit k)))))
  | inr right =>
      cases right with
      | intro tail data =>
          cases data with
          | intro tailUnary tailCont =>
              exact Exists.intro h
                (And.intro uh
                  (And.intro
                    (Exists.intro BHist.Empty
                      (And.intro unary_empty (cont_right_unit h)))
                    (Exists.intro tail (And.intro tailUnary tailCont))))

end BEDC.Derived.NatUp
