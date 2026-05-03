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

theorem DirichletPartSum_term_hsame_transport_deterministic
    {term term' : BHist -> BHist -> BHist} {s s' n S T : BHist}
    (termSame : forall {m : BHist}, UnaryHistory m -> hsame (term m s) (term' m s'))
    (unaryN : UnaryHistory n) :
    DirichletPartSum term s n S -> DirichletPartSum term' s' n T -> hsame S T := by
  intro left right
  have transported := DirichletPartSum_term_hsame_transport termSame unaryN left
  cases transported with
  | intro U data =>
      exact hsame_trans data.right (DirichletPartSum_unary_index_deterministic unaryN data.left right)

theorem DirichletPartSum_exists_unique {term : BHist -> BHist -> BHist} {s n : BHist} :
    UnaryHistory n -> exists S : BHist, DirichletPartSum term s n S ∧
      forall T : BHist, DirichletPartSum term s n T -> hsame S T := by
  intro unaryN
  refine (unary_history_induction
    (P := fun index => exists S : BHist, DirichletPartSum term s index S ∧
      forall T : BHist, DirichletPartSum term s index T -> hsame S T)
    ?base ?step n unaryN)
  · exact Exists.intro BHist.Empty
      (And.intro DirichletPartSum.zero
        (fun T other => by
          cases other
          exact hsame_refl BHist.Empty))
  · intro m unaryM previous
    cases previous with
    | intro S data =>
        have current : DirichletPartSum term s (BHist.e1 m) (append S (term m s)) :=
          DirichletPartSum.step data.left (cont_intro rfl)
        exact Exists.intro (append S (term m s))
          (And.intro current
            (fun T other =>
              DirichletPartSum_unary_index_deterministic
                (unary_e1_closed unaryM) current other))

theorem DirichletPartSum_term_hsame_deterministic
    {term term' : BHist -> BHist -> BHist} {s n S T : BHist} :
    (forall {m : BHist}, UnaryHistory m -> hsame (term m s) (term' m s)) ->
      DirichletPartSum term s n S -> DirichletPartSum term' s n T -> hsame S T := by
  intro pointwise left
  have index_unary :
      forall {m U : BHist}, DirichletPartSum term s m U -> UnaryHistory m := by
    intro m U sum
    induction sum with
    | zero =>
        exact unary_empty
    | step _ _ ih =>
        exact unary_e1_closed ih
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
          have sameTerm := pointwise (index_unary leftSum)
          exact cont_respects_hsame samePartial sameTerm leftStep rightStep

theorem DirichletPartSum_index_unary {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S -> UnaryHistory n := by
  intro sum
  induction sum with
  | zero =>
      exact unary_empty
  | step _ _ ih =>
      exact unary_e1_closed ih

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

theorem DirichletPartSum_nonempty_index_positive {term : BHist -> BHist -> BHist}
    {s n S : BHist} :
    DirichletPartSum term s n S -> (hsame n BHist.Empty -> False) ->
      DirichletPositiveIndex n := by
  intro sum nonemptyN
  have unaryN : UnaryHistory n := DirichletPartSum_index_unary sum
  have tail := BEDC.FKernel.Unary.unary_history_nonempty_e1_tail unaryN nonemptyN
  cases tail with
  | intro t data =>
      exact Exists.intro t (And.intro data.right data.left)

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

theorem DirichletPositiveIndex_append_right_cases {m n : BHist} :
    DirichletPositiveIndex (append m n) ->
      DirichletPositiveIndex m ∨ DirichletPositiveIndex n := by
  intro positiveAppend
  cases positiveAppend with
  | intro tail data =>
      cases data with
      | intro unaryTail appendEq =>
          induction n generalizing m tail with
          | Empty =>
              exact Or.inl (Exists.intro tail (And.intro unaryTail appendEq))
          | e0 n _ =>
              exact False.elim (not_hsame_e0_e1 appendEq)
          | e1 n _ =>
              have appendTailSame : hsame (append m n) tail :=
                hsame_e1_iff.mp appendEq
              have appendUnary : UnaryHistory (append m n) :=
                unary_transport_symm unaryTail appendTailSame
              have rightUnary : UnaryHistory n :=
                unary_append_right_factor appendUnary
              exact Or.inr (Exists.intro n (And.intro rightUnary rfl))

end BEDC.Derived.DirichletSeriesUp
