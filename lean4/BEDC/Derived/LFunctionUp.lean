import BEDC.Derived.DirichletSeriesUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.LFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.DirichletSeriesUp

inductive LFunctionDirichletFiniteZeroTail
    (term : BHist -> BHist -> BHist) (s n : BHist) : BHist -> Prop where
  | empty : LFunctionDirichletFiniteZeroTail term s n BHist.Empty
  | step {k : BHist} :
      LFunctionDirichletFiniteZeroTail term s n k ->
        hsame (term (append n k) s) BHist.Empty ->
          LFunctionDirichletFiniteZeroTail term s n (BHist.e1 k)

theorem LFunctionDirichletPartSum_successor_positive_index
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S -> DirichletPositiveIndex (BHist.e1 n) := by
  intro sum
  have unaryN : UnaryHistory n := by
    induction sum with
    | zero =>
        exact unary_empty
    | step _ _ ih =>
        exact unary_e1_closed ih
  exact Exists.intro n (And.intro unaryN rfl)

theorem LFunctionDirichletPartSum_successor_previous_unique
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s (BHist.e1 n) S ->
      exists P : BHist, DirichletPartSum term s n P ∧ Cont P (term n s) S ∧
        (forall T : BHist, DirichletPartSum term s n T -> hsame P T) := by
  intro sum
  cases sum with
  | step previous stepContinuation =>
      have unaryN : UnaryHistory n := by
        have positiveIndex : DirichletPositiveIndex (BHist.e1 n) :=
          LFunctionDirichletPartSum_successor_positive_index previous
        cases positiveIndex with
        | intro tail data =>
            cases data with
            | intro unaryTail sameSuccessor =>
                cases sameSuccessor
                exact unaryTail
      exact Exists.intro _
        (And.intro previous
          (And.intro stepContinuation
            (fun T other =>
              DirichletPartSum_unary_index_deterministic unaryN previous other)))

theorem LFunctionDirichletPartSum_successor_deterministic
    {term : BHist -> BHist -> BHist} {s n S T : BHist} :
    DirichletPartSum term s (BHist.e1 n) S -> DirichletPartSum term s (BHist.e1 n) T ->
      hsame S T := by
  intro left right
  cases left with
  | step previous stepContinuation =>
      have unaryN : UnaryHistory n := by
        have positiveIndex : DirichletPositiveIndex (BHist.e1 n) :=
          LFunctionDirichletPartSum_successor_positive_index previous
        cases positiveIndex with
        | intro tail data =>
            cases data with
            | intro unaryTail sameSuccessor =>
                cases sameSuccessor
                exact unaryTail
      exact
        DirichletPartSum_unary_index_deterministic (unary_e1_closed unaryN)
          (DirichletPartSum.step previous stepContinuation) right

theorem LFunctionDirichletPartSum_zero_term_successor_stable
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S -> hsame (term n s) BHist.Empty ->
      DirichletPartSum term s (BHist.e1 n) S := by
  intro sum termEmpty
  have stepContinuation : Cont S (term n s) S := by
    exact cont_intro (((congrArg (append S) termEmpty).trans (append_empty_right S)).symm)
  exact DirichletPartSum.step sum stepContinuation

theorem LFunctionDirichletFiniteZeroTail_stability
    {term : BHist -> BHist -> BHist} {s n k S : BHist} :
    DirichletPartSum term s n S -> LFunctionDirichletFiniteZeroTail term s n k ->
      DirichletPartSum term s (append n k) S := by
  intro sum tail
  induction tail with
  | empty =>
      exact sum
  | step previous termEmpty ih =>
      exact LFunctionDirichletPartSum_zero_term_successor_stable ih termEmpty

theorem LFunctionDirichletPartSum_successor_zero_term_previous_result_same
    {term : BHist -> BHist -> BHist} {s n T : BHist} :
    DirichletPartSum term s (BHist.e1 n) T -> hsame (term n s) BHist.Empty ->
      exists P : BHist, DirichletPartSum term s n P ∧ hsame P T := by
  intro sum termEmpty
  cases sum with
  | step previous stepContinuation =>
      have sameResult : hsame T _ :=
        cont_respects_hsame (hsame_refl _) termEmpty stepContinuation
          (cont_right_unit _)
      exact Exists.intro _
        (And.intro previous (hsame_symm sameResult))

theorem LFunctionDirichletPartSum_successor_zero_term_result_iff
    {term : BHist -> BHist -> BHist} {s n T : BHist} :
    hsame (term n s) BHist.Empty ->
      (DirichletPartSum term s (BHist.e1 n) T ↔
        exists P : BHist, DirichletPartSum term s n P ∧ hsame P T) := by
  intro termEmpty
  constructor
  · intro sum
    exact LFunctionDirichletPartSum_successor_zero_term_previous_result_same sum termEmpty
  · intro previousResult
    cases previousResult with
    | intro P data =>
        have stepContinuation : Cont P (term n s) T :=
          cont_hsame_transport (hsame_refl P) (hsame_symm termEmpty) data.right
            (cont_right_unit P)
        exact DirichletPartSum.step data.left stepContinuation

theorem LFunctionDirichletPartSum_zero_terms_result_empty
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    (forall {m : BHist}, UnaryHistory m -> hsame (term m s) BHist.Empty) ->
      DirichletPartSum term s n S -> hsame S BHist.Empty := by
  intro zeroTerm sum
  induction sum with
  | zero =>
      exact hsame_refl BHist.Empty
  | step previous stepContinuation ih =>
      have previousUnary : UnaryHistory _ :=
        DirichletPartSum_index_unary previous
      have currentTermEmpty : hsame (term _ s) BHist.Empty :=
        zeroTerm previousUnary
      exact
        cont_respects_hsame ih currentTermEmpty stepContinuation
          (cont_right_unit BHist.Empty)

theorem LFunctionDirichletPartSum_positive_index_previous_exists
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S -> DirichletPositiveIndex n ->
      exists m P : BHist, n = BHist.e1 m ∧
        DirichletPartSum term s m P ∧ Cont P (term m s) S := by
  intro sum positiveIndex
  have indexCases := DirichletPartSum_index_cases sum
  cases indexCases with
  | inl zeroCase =>
      cases positiveIndex with
      | intro tail positiveData =>
          cases positiveData with
          | intro _unaryTail nEq =>
              cases zeroCase.left
              cases nEq
  | inr successorCase =>
      exact successorCase

theorem LFunctionDirichletPartSum_positive_index_previous_unique
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S -> DirichletPositiveIndex n ->
      exists m P : BHist, n = BHist.e1 m ∧
        DirichletPartSum term s m P ∧ Cont P (term m s) S ∧
          (forall T : BHist, DirichletPartSum term s m T -> hsame P T) := by
  intro sum positiveIndex
  have previousExists :=
    LFunctionDirichletPartSum_positive_index_previous_exists sum positiveIndex
  cases previousExists with
  | intro m previousData =>
      cases previousData with
      | intro P data =>
          have unaryM : UnaryHistory m :=
            DirichletPartSum_index_unary data.right.left
          exact Exists.intro m
            (Exists.intro P
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro data.right.right
                    (fun T other =>
                      DirichletPartSum_unary_index_deterministic unaryM
                        data.right.left other)))))

theorem LFunctionDirichletPartSum_visible_previous_decomposition_deterministic
    {term : BHist -> BHist -> BHist} {s n S m P m' P' : BHist}
    (left : n = BHist.e1 m ∧ DirichletPartSum term s m P ∧ Cont P (term m s) S)
    (right : n = BHist.e1 m' ∧ DirichletPartSum term s m' P' ∧ Cont P' (term m' s) S) :
    m = m' ∧ hsame P P' := by
  cases left with
  | intro leftEq leftRest =>
      cases right with
      | intro rightEq rightRest =>
          cases leftEq
          cases rightEq
          have unaryM : UnaryHistory m := DirichletPartSum_index_unary leftRest.left
          constructor
          · rfl
          · exact DirichletPartSum_unary_index_deterministic unaryM leftRest.left rightRest.left

theorem LFunctionDirichletPartSum_zero_terms_positive_previous_readback
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    (forall {m : BHist}, UnaryHistory m -> hsame (term m s) BHist.Empty) ->
      DirichletPartSum term s n S -> DirichletPositiveIndex n ->
        exists m P : BHist, n = BHist.e1 m ∧ DirichletPartSum term s m P ∧
          hsame P S ∧ (forall T : BHist, DirichletPartSum term s m T -> hsame P T) := by
  intro zeroTerm sum positiveIndex
  have previousData :=
    LFunctionDirichletPartSum_positive_index_previous_exists
      (term := term) (s := s) sum positiveIndex
  cases previousData with
  | intro m rest =>
      cases rest with
      | intro P data =>
          have unaryM : UnaryHistory m :=
            DirichletPartSum_index_unary data.right.left
          have termEmpty : hsame (term m s) BHist.Empty :=
            zeroTerm unaryM
          have samePS : hsame P S := by
            exact hsame_symm
              (cont_respects_hsame (hsame_refl P) termEmpty data.right.right
                (cont_right_unit P))
          have uniqueP :
              forall T : BHist, DirichletPartSum term s m T -> hsame P T := by
            intro T other
            exact
              DirichletPartSum_unary_index_deterministic unaryM data.right.left other
          exact Exists.intro m
            (Exists.intro P
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro samePS uniqueP))))

theorem LFunctionDirichletPartSum_result_hsame_transport
    {term : BHist -> BHist -> BHist} {s n S S' : BHist} :
    hsame S S' ->
      (DirichletPartSum term s n S -> UnaryHistory n) ∧
        (DirichletPartSum term s n S ↔ DirichletPartSum term s n S') := by
  intro sameResult
  constructor
  · intro sum
    exact DirichletPartSum_index_unary sum
  · constructor
    · intro sum
      cases sameResult
      exact sum
    · intro sum
      cases sameResult
      exact sum

theorem LFunctionDirichletPartSum_finite_zero_tail_stability
    {term : BHist -> BHist -> BHist} {s n k S : BHist} :
    DirichletPartSum term s n S ->
      LFunctionDirichletFiniteZeroTail term s n k ->
        DirichletPartSum term s (append n k) S := by
  intro sum zeroTail
  induction zeroTail with
  | empty =>
      exact sum
  | step previous tailEmpty ih =>
      exact LFunctionDirichletPartSum_zero_term_successor_stable ih tailEmpty

inductive DirichletFiniteZeroTail (term : BHist -> BHist -> BHist) (s n : BHist) :
    BHist -> Prop where
  | zero : DirichletFiniteZeroTail term s n BHist.Empty
  | step {k : BHist} :
      DirichletFiniteZeroTail term s n k ->
        hsame (term (append n k) s) BHist.Empty ->
          DirichletFiniteZeroTail term s n (BHist.e1 k)

theorem DirichletFiniteZeroTail_stability
    {term : BHist -> BHist -> BHist} {s n k S : BHist} :
    DirichletPartSum term s n S -> DirichletFiniteZeroTail term s n k ->
      DirichletPartSum term s (append n k) S := by
  intro sum tail
  induction tail with
  | zero =>
      exact sum
  | step previous zeroTerm ih =>
      exact LFunctionDirichletPartSum_zero_term_successor_stable ih zeroTerm

end BEDC.Derived.LFunctionUp
