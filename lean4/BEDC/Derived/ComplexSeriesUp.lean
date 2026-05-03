import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

inductive ComplexPartSum (zero : BHist) (c : BHist -> BHist) : BHist -> BHist -> Prop where
  | zero : ComplexPartSum zero c BHist.Empty zero
  | step {n S T : BHist} :
      ComplexPartSum zero c n S -> Cont S (c n) T -> ComplexPartSum zero c (BHist.e1 n) T

theorem ComplexPartSum_index_cases {zero : BHist} {c : BHist -> BHist} {n S : BHist} :
    ComplexPartSum zero c n S ->
      (n = BHist.Empty ∧ hsame S zero) ∨
        exists m P : BHist, n = BHist.e1 m ∧
          ComplexPartSum zero c m P ∧ Cont P (c m) S := by
  intro sum
  cases sum with
  | zero =>
      exact Or.inl (And.intro rfl (hsame_refl zero))
  | step prev stepCont =>
      exact Or.inr (Exists.intro _ (Exists.intro _
        (And.intro rfl (And.intro prev stepCont))))

theorem ComplexPartSum_deterministic {zero : BHist} {c : BHist -> BHist} {n S T : BHist} :
    ComplexPartSum zero c n S -> ComplexPartSum zero c n T -> hsame S T := by
  intro left
  induction left generalizing T with
  | zero =>
      intro right
      cases right with
      | zero =>
          exact hsame_refl zero
  | step leftSum leftStep ih =>
      intro right
      cases right with
      | step rightSum rightStep =>
          have samePartial := ih rightSum
          exact cont_respects_hsame samePartial (hsame_refl (c _)) leftStep rightStep

theorem ComplexPartSum_successor_term_hsame_deterministic {zero zero' : BHist}
    {c d : BHist -> BHist} {n S T U : BHist} :
    hsame zero zero' -> (forall {m : BHist}, hsame (c m) (d m)) ->
      ComplexPartSum zero c n S -> Cont S (c n) T ->
        ComplexPartSum zero' d (BHist.e1 n) U -> hsame T U := by
  intro sameZero sameTerm previous step final
  have cross :
      forall {m P Q : BHist},
        ComplexPartSum zero c m P -> ComplexPartSum zero' d m Q -> hsame P Q := by
    intro m P Q left
    induction left generalizing Q with
    | zero =>
        intro right
        cases right with
        | zero =>
            exact sameZero
    | step leftSum leftStep ih =>
        intro right
        cases right with
        | step rightSum rightStep =>
            have samePartial := ih rightSum
            exact cont_respects_hsame samePartial sameTerm leftStep rightStep
  cases final with
  | step finalPrevious finalStep =>
      have samePrevious := cross previous finalPrevious
      exact cont_respects_hsame samePrevious sameTerm step finalStep

theorem ComplexPartSum_term_hsame_transport {zero zero' : BHist} {c d : BHist -> BHist}
    (zeroSame : hsame zero zero')
    (termSame : forall {n : BHist}, UnaryHistory n -> hsame (c n) (d n))
    {n S : BHist} :
    UnaryHistory n -> ComplexPartSum zero c n S ->
      exists T : BHist, ComplexPartSum zero' d n T /\ hsame S T := by
  intro unaryN sum
  induction sum with
  | zero =>
      exact Exists.intro zero' (And.intro ComplexPartSum.zero zeroSame)
  | step previous stepContinuation ih =>
      have unaryPrevious : UnaryHistory _ := unary_e1_inversion unaryN
      have transportedPrevious := ih unaryPrevious
      cases transportedPrevious with
      | intro previous' previousData =>
          have resultSame :
              hsame _ (append previous' (d _)) :=
            cont_respects_hsame previousData.right (termSame unaryPrevious) stepContinuation
              (cont_intro rfl)
          exact Exists.intro (append previous' (d _))
            (And.intro (ComplexPartSum.step previousData.left (cont_intro rfl)) resultSame)

theorem ComplexPartSum_pointwise_hsame_deterministic {zero zero' : BHist}
    {c d : BHist -> BHist} {n S T : BHist} :
    hsame zero zero' ->
      (∀ {m : BHist}, UnaryHistory m -> hsame (c m) (d m)) ->
        UnaryHistory n -> ComplexPartSum zero c n S -> ComplexPartSum zero' d n T ->
          hsame S T := by
  intro sameZero pointwise unaryN left
  induction left generalizing T with
  | zero =>
      intro right
      cases right with
      | zero => exact sameZero
  | step leftPrev leftStep ih =>
      intro right
      cases right with
      | step rightPrev rightStep =>
          have unaryTail : UnaryHistory _ := unary_history_e1_iff.mp unaryN
          have samePrev := ih unaryTail rightPrev
          exact cont_respects_hsame samePrev (pointwise unaryTail) leftStep rightStep

inductive ComplexAbsPartSum (zero : BHist) (modulus : BHist -> BHist) :
    BHist -> BHist -> Prop where
  | zero : ComplexAbsPartSum zero modulus BHist.Empty zero
  | step {n M T : BHist} :
      ComplexAbsPartSum zero modulus n M -> Cont M (modulus n) T ->
        ComplexAbsPartSum zero modulus (BHist.e1 n) T

theorem ComplexAbsPartSum_successor_result_deterministic {zero : BHist}
    {modulus : BHist -> BHist} {n M T U : BHist} :
    ComplexAbsPartSum zero modulus n M -> Cont M (modulus n) T ->
      ComplexAbsPartSum zero modulus (BHist.e1 n) U -> hsame T U := by
  have deterministic :
      forall {n S T : BHist},
        ComplexAbsPartSum zero modulus n S -> ComplexAbsPartSum zero modulus n T -> hsame S T := by
    intro n S T left
    induction left generalizing T with
    | zero =>
        intro right
        cases right with
        | zero =>
            exact hsame_refl zero
    | step leftSum leftStep ih =>
        intro right
        cases right with
        | step rightSum rightStep =>
            have samePartial := ih rightSum
            exact cont_respects_hsame samePartial (hsame_refl (modulus _)) leftStep rightStep
  intro previous step final
  cases final with
  | step finalPrevious finalStep =>
      have samePrevious := deterministic previous finalPrevious
      exact cont_respects_hsame samePrevious (hsame_refl (modulus n)) step finalStep

theorem ComplexPartSum_term_hsame_deterministic {zero : BHist} {c d : BHist -> BHist}
    {n S T : BHist} :
    (forall {m : BHist}, UnaryHistory m -> hsame (c m) (d m)) ->
      ComplexPartSum zero c n S -> ComplexPartSum zero d n T -> hsame S T := by
  intro pointwise left
  have index_unary :
      forall {m U : BHist}, ComplexPartSum zero c m U -> UnaryHistory m := by
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
          exact hsame_refl zero
  | step leftSum leftStep ih =>
      intro right
      cases right with
      | step rightSum rightStep =>
          have samePartial := ih rightSum
          have sameTerm := pointwise (index_unary leftSum)
          exact cont_respects_hsame samePartial sameTerm leftStep rightStep

theorem ComplexAbsPartSum_pointwise_hsame_deterministic {zero zero' : BHist}
    {modulus modulus' : BHist -> BHist} {n M T : BHist} :
    hsame zero zero' ->
      (∀ {m : BHist}, UnaryHistory m -> hsame (modulus m) (modulus' m)) ->
        UnaryHistory n -> ComplexAbsPartSum zero modulus n M ->
          ComplexAbsPartSum zero' modulus' n T -> hsame M T := by
  intro sameZero pointwise unaryN left
  induction left generalizing T with
  | zero =>
      intro right
      cases right with
      | zero => exact sameZero
  | step leftPrev leftStep ih =>
      intro right
      cases right with
      | step rightPrev rightStep =>
          have unaryTail : UnaryHistory _ := unary_history_e1_iff.mp unaryN
          have samePrev := ih unaryTail rightPrev
          exact cont_respects_hsame samePrev (pointwise unaryTail) leftStep rightStep

theorem ComplexAbsPartSum_successor_modulus_hsame_deterministic {zero zero' : BHist}
    {modulus modulus' : BHist -> BHist} {n M T U : BHist} :
    hsame zero zero' -> (forall {m : BHist}, hsame (modulus m) (modulus' m)) ->
      ComplexAbsPartSum zero modulus n M -> Cont M (modulus n) T ->
        ComplexAbsPartSum zero' modulus' (BHist.e1 n) U -> hsame T U := by
  intro sameZero sameModulus previous step final
  have cross :
      forall {m P Q : BHist},
        ComplexAbsPartSum zero modulus m P ->
          ComplexAbsPartSum zero' modulus' m Q -> hsame P Q := by
    intro m P Q left
    induction left generalizing Q with
    | zero =>
        intro right
        cases right with
        | zero =>
            exact sameZero
    | step leftSum leftStep ih =>
        intro right
        cases right with
        | step rightSum rightStep =>
            have samePartial := ih rightSum
            exact cont_respects_hsame samePartial sameModulus leftStep rightStep
  cases final with
  | step finalPrevious finalStep =>
      have samePrevious := cross previous finalPrevious
      exact cont_respects_hsame samePrevious sameModulus step finalStep

def ComplexTermSeqCarrier (c : BHist -> BHist) : Prop :=
  forall n : BHist, UnaryHistory n -> ComplexHistoryCarrier (c n)

theorem ComplexTermSeqCarrier_hsame_transport {c d : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (c n) (d n)) ->
      ComplexTermSeqCarrier c -> ComplexTermSeqCarrier d := by
  intro pointwise carrier n unaryN
  cases carrier n unaryN with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier cont =>
                  exact Exists.intro real
                    (Exists.intro imag
                      (And.intro realCarrier
                        (And.intro imagCarrier
                          (cont_result_hsame_transport cont (pointwise unaryN)))))

end BEDC.Derived.ComplexSeriesUp
