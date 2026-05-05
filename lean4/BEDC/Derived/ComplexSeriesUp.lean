import BEDC.Derived.ComplexLimitUp
import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexLimitUp
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

theorem ComplexPartSum_visible_previous_decomposition_deterministic
    {zero : BHist} {c : BHist -> BHist} {n S m P m' P' : BHist}
    (left : n = BHist.e1 m ∧ ComplexPartSum zero c m P ∧ Cont P (c m) S)
    (right : n = BHist.e1 m' ∧ ComplexPartSum zero c m' P' ∧ Cont P' (c m') S) :
    m = m' ∧ hsame P P' := by
  cases left with
  | intro leftEq leftRest =>
      cases right with
      | intro rightEq rightRest =>
          cases leftEq
          cases rightEq
          constructor
          · rfl
          · exact ComplexPartSum_deterministic leftRest.left rightRest.left

theorem ComplexPartSum_exists_unique {zero : BHist} {c : BHist -> BHist} {n : BHist} :
    UnaryHistory n -> exists S : BHist, ComplexPartSum zero c n S ∧
      forall T : BHist, ComplexPartSum zero c n T -> hsame S T := by
  intro unaryN
  refine (unary_history_induction
    (P := fun index => exists S : BHist, ComplexPartSum zero c index S ∧
      forall T : BHist, ComplexPartSum zero c index T -> hsame S T)
    ?base ?step n unaryN)
  · exact Exists.intro zero
      (And.intro ComplexPartSum.zero
        (fun T other => ComplexPartSum_deterministic ComplexPartSum.zero other))
  · intro m _unaryM previous
    cases previous with
    | intro S data =>
        have current : ComplexPartSum zero c (BHist.e1 m) (append S (c m)) :=
          ComplexPartSum.step data.left (cont_intro rfl)
        exact Exists.intro (append S (c m))
          (And.intro current
            (fun T other => ComplexPartSum_deterministic current other))

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

theorem ComplexPartSum_result_nonempty_of_nonempty_terms {zero : BHist}
    {c : BHist -> BHist} {n S : BHist} :
    (hsame zero BHist.Empty -> False) ->
      (forall {m : BHist}, UnaryHistory m -> hsame (c m) BHist.Empty -> False) ->
        ComplexPartSum zero c n S -> hsame S BHist.Empty -> False := by
  intro zeroNonempty termNonempty sum
  have indexUnary :
      forall {m P : BHist}, ComplexPartSum zero c m P -> UnaryHistory m :=
    fun {m P : BHist} (part : ComplexPartSum zero c m P) => by
      induction part with
      | zero =>
          exact unary_empty
      | step _ _ ih =>
          exact unary_e1_closed ih
  induction sum with
  | zero =>
      intro resultEmpty
      exact zeroNonempty resultEmpty
  | step previous stepContinuation _ih =>
      intro resultEmpty
      have emptyStep :
          Cont _ (c _) BHist.Empty :=
        cont_result_hsame_transport stepContinuation resultEmpty
      have emptyParts := cont_empty_result_inversion emptyStep
      exact termNonempty (indexUnary previous) emptyParts.right

theorem ComplexPartSum_result_unary {zero : BHist} {c : BHist -> BHist} {n S : BHist}
    (zeroUnary : UnaryHistory zero)
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (c m)) :
    ComplexPartSum zero c n S -> UnaryHistory S := by
  intro sum
  induction sum with
  | zero =>
      exact zeroUnary
  | step previous stepContinuation ih =>
      have indexUnary :
          forall {m P : BHist}, ComplexPartSum zero c m P -> UnaryHistory m := by
        intro m P previousSum
        induction previousSum with
        | zero =>
            exact unary_empty
        | step _ _ inner =>
            exact unary_e1_closed inner
      exact unary_cont_closed ih (termUnary (indexUnary previous)) stepContinuation

theorem ComplexPartSum_semanticNameCert {zero : BHist} {c : BHist -> BHist}
    {n S : BHist} (sum : ComplexPartSum zero c n S) :
    SemanticNameCert (fun result : BHist => ComplexPartSum zero c n result)
      (fun result : BHist => ComplexPartSum zero c n result)
      (fun result : BHist => ComplexPartSum zero c n result) hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro S sum
      equiv_refl := by
        intro result _source
        exact hsame_refl result
      equiv_symm := by
        intro result result' sameResult
        exact hsame_symm sameResult
      equiv_trans := by
        intro result result' result'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro result result' sameResult source
        cases sameResult
        exact source
    }
    pattern_sound := by
      intro result source
      exact source
    ledger_sound := by
      intro result source
      exact source
  }

inductive ComplexAbsPartSum (zero : BHist) (modulus : BHist -> BHist) :
    BHist -> BHist -> Prop where
  | zero : ComplexAbsPartSum zero modulus BHist.Empty zero
  | step {n M T : BHist} :
      ComplexAbsPartSum zero modulus n M -> Cont M (modulus n) T ->
        ComplexAbsPartSum zero modulus (BHist.e1 n) T

theorem ComplexAbsPartSum_index_cases {zero : BHist} {modulus : BHist -> BHist}
    {n M : BHist} :
    ComplexAbsPartSum zero modulus n M ->
      (n = BHist.Empty ∧ hsame M zero) ∨
        exists m P : BHist, n = BHist.e1 m ∧
          ComplexAbsPartSum zero modulus m P ∧ Cont P (modulus m) M := by
  intro sum
  cases sum with
  | zero =>
      exact Or.inl (And.intro rfl (hsame_refl zero))
  | step prev stepCont =>
      exact Or.inr (Exists.intro _ (Exists.intro _
        (And.intro rfl (And.intro prev stepCont))))

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

theorem ComplexAbsPartSum_modulus_hsame_deterministic {zero : BHist}
    {modulus modulus' : BHist -> BHist} {n M T : BHist} :
    (forall {m : BHist}, UnaryHistory m -> hsame (modulus m) (modulus' m)) ->
      ComplexAbsPartSum zero modulus n M -> ComplexAbsPartSum zero modulus' n T -> hsame M T := by
  intro pointwise left
  have index_unary :
      forall {m U : BHist}, ComplexAbsPartSum zero modulus m U -> UnaryHistory m := by
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
          have sameModulus := pointwise (index_unary leftSum)
          exact cont_respects_hsame samePartial sameModulus leftStep rightStep

theorem ComplexAbsPartSum_modulus_hsame_transport {zero zero' : BHist}
    {modulus modulus' : BHist -> BHist}
    (zeroSame : hsame zero zero')
    (modulusSame : forall {n : BHist}, UnaryHistory n -> hsame (modulus n) (modulus' n))
    {n M : BHist} :
    UnaryHistory n -> ComplexAbsPartSum zero modulus n M ->
      exists T : BHist, ComplexAbsPartSum zero' modulus' n T /\ hsame M T := by
  intro unaryN sum
  induction sum with
  | zero =>
      exact Exists.intro zero' (And.intro ComplexAbsPartSum.zero zeroSame)
  | step previous stepContinuation ih =>
      have unaryPrevious : UnaryHistory _ := unary_e1_inversion unaryN
      have transportedPrevious := ih unaryPrevious
      cases transportedPrevious with
      | intro previous' previousData =>
          have resultSame :
              hsame _ (append previous' (modulus' _)) :=
            cont_respects_hsame previousData.right (modulusSame unaryPrevious)
              stepContinuation (cont_intro rfl)
          exact Exists.intro (append previous' (modulus' _))
            (And.intro (ComplexAbsPartSum.step previousData.left (cont_intro rfl)) resultSame)

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

theorem ComplexAbsPartSum_unary_index_deterministic {zero : BHist}
    {modulus : BHist -> BHist} {n S T : BHist} :
    UnaryHistory n -> ComplexAbsPartSum zero modulus n S ->
      ComplexAbsPartSum zero modulus n T -> hsame S T := by
  intro unaryN left
  induction left generalizing T with
  | zero =>
      intro right
      cases right with
      | zero =>
          exact hsame_refl zero
  | step leftSum leftStep ih =>
      intro right
      have unaryPrev := unary_e1_inversion unaryN
      cases right with
      | step rightSum rightStep =>
          have samePartial := ih unaryPrev rightSum
          exact cont_respects_hsame samePartial (hsame_refl (modulus _)) leftStep rightStep

theorem ComplexAbsPartSum_exists_unique {zero : BHist} {modulus : BHist -> BHist}
    {n : BHist} :
    UnaryHistory n -> exists M : BHist, ComplexAbsPartSum zero modulus n M ∧
      forall T : BHist, ComplexAbsPartSum zero modulus n T -> hsame M T := by
  intro unaryN
  refine (unary_history_induction
    (P := fun index => exists M : BHist, ComplexAbsPartSum zero modulus index M ∧
      forall T : BHist, ComplexAbsPartSum zero modulus index T -> hsame M T)
    ?base ?step n unaryN)
  · exact Exists.intro zero
      (And.intro ComplexAbsPartSum.zero
        (fun T other =>
          ComplexAbsPartSum_unary_index_deterministic unary_empty ComplexAbsPartSum.zero other))
  · intro m unaryM previous
    cases previous with
    | intro M data =>
        have current : ComplexAbsPartSum zero modulus (BHist.e1 m) (append M (modulus m)) :=
          ComplexAbsPartSum.step data.left (cont_intro rfl)
        exact Exists.intro (append M (modulus m))
          (And.intro current
            (fun T other =>
              ComplexAbsPartSum_unary_index_deterministic (unary_e1_closed unaryM) current other))

theorem ComplexAbsPartSum_result_unary {zero : BHist} {modulus : BHist -> BHist}
    {n M : BHist}
    (zeroUnary : UnaryHistory zero)
    (modulusUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (modulus m)) :
    ComplexAbsPartSum zero modulus n M -> UnaryHistory M := by
  intro sum
  induction sum with
  | zero =>
      exact zeroUnary
  | step previous stepContinuation ih =>
      have indexUnary :
          forall {m P : BHist}, ComplexAbsPartSum zero modulus m P -> UnaryHistory m := by
        intro m P previousSum
        induction previousSum with
        | zero =>
            exact unary_empty
        | step _ _ inner =>
            exact unary_e1_closed inner
      exact unary_cont_closed ih (modulusUnary (indexUnary previous)) stepContinuation

theorem ComplexAbsPartSum_result_nonempty_of_nonempty_terms {zero : BHist}
    {modulus : BHist -> BHist} {n M : BHist} :
    (hsame zero BHist.Empty -> False) ->
      (forall {m : BHist}, UnaryHistory m -> hsame (modulus m) BHist.Empty -> False) ->
        ComplexAbsPartSum zero modulus n M -> hsame M BHist.Empty -> False := by
  intro zeroNonempty modulusNonempty sum
  have indexUnary :
      forall {m P : BHist}, ComplexAbsPartSum zero modulus m P -> UnaryHistory m :=
    fun {m P : BHist} (part : ComplexAbsPartSum zero modulus m P) => by
      induction part with
      | zero =>
          exact unary_empty
      | step _ _ ih =>
          exact unary_e1_closed ih
  induction sum with
  | zero =>
      intro resultEmpty
      exact zeroNonempty resultEmpty
  | step previous stepContinuation _ih =>
      intro resultEmpty
      have emptyStep :
          Cont _ (modulus _) BHist.Empty :=
        cont_result_hsame_transport stepContinuation resultEmpty
      have emptyParts := cont_empty_result_inversion emptyStep
      exact modulusNonempty (indexUnary previous) emptyParts.right

theorem ComplexAbsPartSum_empty_result_boundary {zero : BHist} {modulus : BHist -> BHist}
    {n M : BHist} :
    ComplexAbsPartSum zero modulus n M -> hsame M BHist.Empty ->
      hsame zero BHist.Empty ∨
        exists m : BHist, UnaryHistory m ∧ hsame (modulus m) BHist.Empty := by
  intro sum
  have indexUnary :
      forall {m P : BHist}, ComplexAbsPartSum zero modulus m P -> UnaryHistory m :=
    fun {m P : BHist} (part : ComplexAbsPartSum zero modulus m P) => by
      induction part with
      | zero =>
          exact unary_empty
      | step _ _ ih =>
          exact unary_e1_closed ih
  induction sum with
  | zero =>
      intro resultEmpty
      exact Or.inl resultEmpty
  | step previous stepContinuation _ih =>
      intro resultEmpty
      have emptyStep :
          Cont _ (modulus _) BHist.Empty :=
        cont_result_hsame_transport stepContinuation resultEmpty
      have emptyParts := cont_empty_result_inversion emptyStep
      exact Or.inr (Exists.intro _
        (And.intro (indexUnary previous) emptyParts.right))

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

theorem ComplexAbsPartSum_modulus_successor_result_deterministic {zero : BHist}
    {modulus modulus' : BHist -> BHist} {n M T U : BHist} :
    (forall m : BHist, hsame (modulus m) (modulus' m)) ->
      ComplexAbsPartSum zero modulus n M -> Cont M (modulus n) T ->
        ComplexAbsPartSum zero modulus' (BHist.e1 n) U -> hsame T U := by
  intro pointwise previous step final
  have deterministic :
      forall {n S T : BHist},
        ComplexAbsPartSum zero modulus n S -> ComplexAbsPartSum zero modulus' n T -> hsame S T := by
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
            exact cont_respects_hsame samePartial (pointwise _) leftStep rightStep
  cases final with
  | step finalPrevious finalStep =>
      have samePrevious := deterministic previous finalPrevious
      exact cont_respects_hsame samePrevious (pointwise n) step finalStep
theorem ComplexAbsPartSum_modulus_hsame_successor_result {zero zero' : BHist}
    {modulus modulus' : BHist -> BHist} (zeroSame : hsame zero zero')
    (modulusSame : forall {n : BHist}, hsame (modulus n) (modulus' n))
    {n M M' T T' : BHist} :
    ComplexAbsPartSum zero modulus n M -> ComplexAbsPartSum zero' modulus' n M' ->
      Cont M (modulus n) T -> Cont M' (modulus' n) T' -> hsame T T' := by
  intro left
  induction left generalizing M' T T' with
  | zero =>
      intro right leftStep rightStep
      cases right with
      | zero =>
          exact cont_respects_hsame zeroSame modulusSame leftStep rightStep
  | step leftSum leftStep ih =>
      intro right successorLeft successorRight
      cases right with
      | step rightSum rightStep =>
          have samePrevious := ih rightSum leftStep rightStep
          exact cont_respects_hsame samePrevious modulusSame successorLeft successorRight

def ComplexTermSeqCarrier (c : BHist -> BHist) : Prop :=
  forall n : BHist, UnaryHistory n -> ComplexHistoryCarrier (c n)

def ComplexSeriesConvWitness (zero : BHist) (c s N M : BHist -> BHist) (limit : BHist) : Prop :=
  ComplexTermSeqCarrier c ∧
    (forall n : BHist, UnaryHistory n -> ComplexPartSum zero c n (s n)) ∧
      ComplexLimit s N limit M

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

def ComplexSeriesConv (zero : BHist) (c : BHist -> BHist) (S : BHist) : Prop :=
  exists ps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
    (forall n : BHist, UnaryHistory n -> ComplexPartSum zero c n (ps n)) /\
      ComplexLimit ps N S M

theorem complex_series_semantic_name_certificate {zero : BHist} {c : BHist -> BHist}
    {S : BHist} :
    ComplexSeriesConv zero c S ->
      SemanticNameCert (ComplexSeriesConv zero c) (ComplexSeriesConv zero c)
        (ComplexSeriesConv zero c) hsame := by
  intro conv
  exact {
    core := {
      carrier_inhabited := Exists.intro S conv
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
        cases carrier with
        | intro ps carrierRest =>
            cases carrierRest with
            | intro N carrierRest =>
                cases carrierRest with
                | intro M data =>
                    exact Exists.intro ps
                      (Exists.intro N
                        (Exists.intro M
                          (And.intro data.left
                            (ComplexLimit_hsame_transport same data.right))))
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.ComplexSeriesUp
