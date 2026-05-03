import BEDC.Derived.ComplexSeriesUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirichletSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

inductive DirichletPartSum (term : BHist -> BHist -> BHist) (s : BHist) :
    BHist -> BHist -> Prop where
  | zero : DirichletPartSum term s BHist.Empty BHist.Empty
  | step {n S T : BHist} :
      DirichletPartSum term s n S -> Cont S (term n s) T ->
        DirichletPartSum term s (BHist.e1 n) T

theorem DirichletPartSum_index_cases
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S ->
      (n = BHist.Empty ∧ hsame S BHist.Empty) ∨
        exists m P : BHist, n = BHist.e1 m ∧
          DirichletPartSum term s m P ∧ Cont P (term m s) S := by
  intro sum
  cases sum with
  | zero =>
      exact Or.inl (And.intro rfl (hsame_refl BHist.Empty))
  | step prev stepCont =>
      exact Or.inr (Exists.intro _ (Exists.intro _
        (And.intro rfl (And.intro prev stepCont))))

theorem DirichletPartSum_successor_result_deterministic
    {term : BHist -> BHist -> BHist} {s n S T U : BHist} :
    DirichletPartSum term s n S -> Cont S (term n s) T ->
      DirichletPartSum term s (BHist.e1 n) U -> hsame T U := by
  have deterministic :
      forall {n S T : BHist},
        DirichletPartSum term s n S -> DirichletPartSum term s n T -> hsame S T := by
    intro n S T left
    induction left generalizing T with
    | zero =>
        intro right
        cases right with
        | zero =>
            exact hsame_refl BHist.Empty
    | step leftSum leftStep ih =>
        intro right
        cases right with
        | step rightSum rightStep =>
            have samePartial := ih rightSum
            exact cont_respects_hsame samePartial (hsame_refl (term _ s)) leftStep rightStep
  intro previous step final
  cases final with
  | step finalPrevious finalStep =>
      have samePrevious := deterministic previous finalPrevious
      exact cont_respects_hsame samePrevious (hsame_refl (term n s)) step finalStep

theorem DirichletPartSum_term_hsame_transport {term term' : BHist -> BHist -> BHist}
    {s s' : BHist}
    (termSame : forall {n : BHist}, UnaryHistory n -> hsame (term n s) (term' n s'))
    {n S : BHist} :
    UnaryHistory n -> DirichletPartSum term s n S ->
      exists T : BHist, DirichletPartSum term' s' n T /\ hsame S T := by
  intro unaryN sum
  induction sum with
  | zero =>
      exact Exists.intro BHist.Empty
        (And.intro DirichletPartSum.zero (hsame_refl BHist.Empty))
  | step previous stepContinuation ih =>
      have unaryPrevious : UnaryHistory _ := unary_e1_inversion unaryN
      have transportedPrevious := ih unaryPrevious
      cases transportedPrevious with
      | intro previous' previousData =>
          have resultSame :
              hsame _ (append previous' (term' _ s')) :=
            cont_respects_hsame previousData.right (termSame unaryPrevious) stepContinuation
              (cont_intro rfl)
          exact Exists.intro (append previous' (term' _ s'))
            (And.intro (DirichletPartSum.step previousData.left (cont_intro rfl)) resultSame)

theorem DirichletPartSum_unary_index_deterministic
    {term : BHist -> BHist -> BHist} {s n S T : BHist} :
    UnaryHistory n -> DirichletPartSum term s n S ->
      DirichletPartSum term s n T -> hsame S T := by
  intro unaryN left
  induction left generalizing T with
  | zero =>
      intro right
      cases right with
      | zero =>
          exact hsame_refl BHist.Empty
  | step leftSum leftStep ih =>
      intro right
      have unaryPrev := unary_e1_inversion unaryN
      cases right with
      | step rightSum rightStep =>
          have samePartial := ih unaryPrev rightSum
          exact cont_respects_hsame samePartial (hsame_refl (term _ s)) leftStep rightStep

theorem DirichletSeriesIndex_e1_tail_nonempty {n : BHist} :
    UnaryHistory n ->
      UnaryHistory (BHist.e1 n) ∧ (hsame (BHist.e1 n) BHist.Empty -> False) := by
  intro unaryN
  constructor
  · exact unary_e1_closed unaryN
  · intro sameTail
    exact not_hsame_e1_empty sameTail

theorem DirichletSeriesIndex_append_unary_tail_nonempty {n tail : BHist} :
    UnaryHistory n -> (hsame n BHist.Empty -> False) -> UnaryHistory tail ->
      UnaryHistory (append n tail) ∧ (hsame (append n tail) BHist.Empty -> False) := by
  intro unaryN nNonempty unaryTail
  constructor
  · exact unary_append_closed unaryN unaryTail
  · intro appendEmpty
    exact nNonempty (append_eq_empty_iff.mp appendEmpty).left

def DirichletPositiveIndex (n : BHist) : Prop :=
  exists tail : BHist, UnaryHistory tail /\ n = BHist.e1 tail

theorem DirichletPositiveIndex_append_unary_closed {m n : BHist} :
    DirichletPositiveIndex m -> UnaryHistory n -> DirichletPositiveIndex (append m n) := by
  intro positiveM unaryN
  cases positiveM with
  | intro tail data =>
      cases data with
      | intro unaryTail mEq =>
          cases mEq
          exact Exists.intro (append tail n)
            (And.intro (unary_append_closed unaryTail unaryN)
              (unary_append_e1_left (h := n) (k := tail) unaryN))

end BEDC.Derived.DirichletSeriesUp
