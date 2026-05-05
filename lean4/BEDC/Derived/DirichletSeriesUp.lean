import BEDC.Derived.ComplexSeriesUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirichletSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.ComplexUp

def DirichletTerm (coeff : BHist -> BHist) (n s : BHist) : BHist :=
  append (coeff n) s

theorem DirichletTerm_complex_carrier_well_defined {coeff : BHist -> BHist} {n s : BHist} :
    UnaryHistory n -> ComplexHistoryCarrier (coeff n) -> ComplexHistoryCarrier s ->
      ComplexHistoryCarrier (DirichletTerm coeff n s) := by
  intro _unaryN coeffCarrier sCarrier
  unfold DirichletTerm
  exact ComplexHistoryCarrier_append_unary_closed coeffCarrier
    (ComplexHistoryCarrier_unary sCarrier)

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

theorem DirichletPartSum_successor_term_nonempty_result_nonempty
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s (BHist.e1 n) S -> (hsame (term n s) BHist.Empty -> False) ->
      (hsame S BHist.Empty -> False) := by
  intro sum termNonempty resultEmpty
  cases sum with
  | step _previous stepContinuation =>
      have emptyContinuation : Cont _ (term n s) BHist.Empty :=
        cont_result_hsame_transport stepContinuation resultEmpty
      have emptyParts := cont_empty_result_inversion emptyContinuation
      exact termNonempty emptyParts.right

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

theorem DirichletPartSum_complexPartSum {term : BHist -> BHist -> BHist}
    {s n S : BHist} :
    DirichletPartSum term s n S ->
      BEDC.Derived.ComplexSeriesUp.ComplexPartSum BHist.Empty
        (fun m : BHist => term m s) n S := by
  intro sum
  induction sum with
  | zero =>
      exact BEDC.Derived.ComplexSeriesUp.ComplexPartSum.zero
  | step _previous stepContinuation ih =>
      exact BEDC.Derived.ComplexSeriesUp.ComplexPartSum.step ih stepContinuation

theorem DirichletPartSum_successor_result_nonempty {term : BHist -> BHist -> BHist}
    {s n S : BHist} :
    (forall {m : BHist}, UnaryHistory m -> hsame (term m s) BHist.Empty -> False) ->
      DirichletPartSum term s (BHist.e1 n) S -> hsame S BHist.Empty -> False := by
  intro termNonempty sum resultEmpty
  cases sum with
  | step previous stepContinuation =>
      have emptyStep : Cont _ _ BHist.Empty :=
        cont_result_hsame_transport stepContinuation resultEmpty
      have emptyTerm : hsame (term n s) BHist.Empty :=
        (cont_empty_result_inversion emptyStep).right
      exact termNonempty (DirichletPartSum_index_unary previous) emptyTerm

theorem DirichletPartSum_result_unary {term : BHist -> BHist -> BHist} {s n S : BHist}
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (term m s)) :
    DirichletPartSum term s n S -> UnaryHistory S := by
  intro sum
  induction sum with
  | zero =>
      exact unary_empty
  | step previous stepContinuation ih =>
      have unaryPreviousIndex : UnaryHistory _ := DirichletPartSum_index_unary previous
      exact unary_cont_closed ih (termUnary unaryPreviousIndex) stepContinuation

theorem DirichletPartSum_semanticNameCert {term : BHist -> BHist -> BHist} {s n S : BHist}
    (sum : DirichletPartSum term s n S) :
    SemanticNameCert (fun result : BHist => DirichletPartSum term s n result)
      (fun result : BHist => DirichletPartSum term s n result)
      (fun result : BHist => DirichletPartSum term s n result) hsame := by
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

theorem DirichletTerm_positive_index_append_hsame_transport
    {coeff coeff' : BHist -> BHist} {n n' s s' t t' : BHist} :
    DirichletPositiveIndex n -> DirichletPositiveIndex n' ->
      hsame t (append (coeff n) s) -> hsame t' (append (coeff' n') s') ->
        hsame (coeff n) (coeff' n') -> hsame s s' ->
          hsame t t' ∧ hsame t (DirichletTerm coeff n s) ∧
            hsame t' (DirichletTerm coeff' n' s') := by
  intro _positiveN _positiveN' sameT sameT' sameCoeff sameS
  have sameTerms : hsame (append (coeff n) s) (append (coeff' n') s') := by
    exact hsame_trans (congrArg (fun x : BHist => append x s) sameCoeff)
      (congrArg (append (coeff' n')) sameS)
  exact And.intro (hsame_trans sameT (hsame_trans sameTerms (hsame_symm sameT')))
    (And.intro sameT sameT')

def DirichletCoefficient_completely_multiplicative (coeff : BHist -> BHist) : Prop :=
  hsame (coeff (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) ∧
    forall {m n : BHist}, DirichletPositiveIndex m -> DirichletPositiveIndex n ->
      hsame (coeff (append m n)) (append (coeff m) (coeff n))

theorem DirichletPositiveIndex_nonempty {n : BHist} :
    DirichletPositiveIndex n -> (hsame n BHist.Empty -> False) := by
  intro positiveN sameEmpty
  cases positiveN with
  | intro tail data =>
      cases data with
      | intro _unaryTail nEq =>
          cases nEq
          exact not_hsame_e1_empty sameEmpty

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

theorem DirichletPartSum_positive_index_result_nonempty
    {term : BHist -> BHist -> BHist} {s n S : BHist}
    (termNonempty : forall {m : BHist}, UnaryHistory m ->
      hsame (term m s) BHist.Empty -> False) :
    DirichletPartSum term s n S -> DirichletPositiveIndex n ->
      hsame S BHist.Empty -> False := by
  intro sum positive sameEmpty
  cases positive with
  | intro tail data =>
      cases data with
      | intro unaryTail nEq =>
          cases nEq
          cases sum with
          | step previous stepCont =>
              have emptyStep : Cont _ (term tail s) BHist.Empty :=
                cont_result_hsame_transport stepCont sameEmpty
              have endpoints := cont_empty_result_inversion emptyStep
              exact termNonempty unaryTail endpoints.right

theorem DirichletPartSum_positive_index_predecessor {term : BHist -> BHist -> BHist}
    {s n S : BHist} :
    DirichletPartSum term s n S -> DirichletPositiveIndex n ->
      exists m P : BHist, n = BHist.e1 m ∧ UnaryHistory m ∧
        DirichletPartSum term s m P ∧ Cont P (term m s) S := by
  intro sum positiveN
  cases sum with
  | zero =>
      exact False.elim (DirichletPositiveIndex_nonempty positiveN (hsame_refl BHist.Empty))
  | step previous stepCont =>
      exact Exists.intro _ (Exists.intro _
        (And.intro rfl
          (And.intro (DirichletPartSum_index_unary previous)
            (And.intro previous stepCont))))

theorem DirichletPartSum_append_successor_predecessor
    {term : BHist -> BHist -> BHist} {s m n S : BHist} :
    DirichletPartSum term s (append m (BHist.e1 n)) S ->
      ∃ P : BHist, DirichletPartSum term s (append m n) P ∧
        Cont P (term (append m n) s) S := by
  intro sum
  cases sum with
  | step previous stepCont =>
      exact Exists.intro _ (And.intro previous stepCont)

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

theorem DirichletPositiveIndex_prepend_unary_closed {m n : BHist} :
    UnaryHistory m -> DirichletPositiveIndex n -> DirichletPositiveIndex (append m n) := by
  intro unaryM positiveN
  cases positiveN with
  | intro tail data =>
      cases data with
      | intro unaryTail nEq =>
          cases nEq
          exact Exists.intro (append m tail)
            (And.intro (unary_append_closed unaryM unaryTail) rfl)

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

theorem DirichletPositiveIndex_append_iff {m n : BHist} :
    UnaryHistory m -> UnaryHistory n ->
      (DirichletPositiveIndex (append m n) ↔
        DirichletPositiveIndex m ∨ DirichletPositiveIndex n) := by
  intro unaryM unaryN
  constructor
  · intro positiveAppend
    exact DirichletPositiveIndex_append_right_cases positiveAppend
  · intro positive
    cases positive with
    | inl positiveM =>
        exact DirichletPositiveIndex_append_unary_closed positiveM unaryN
    | inr positiveN =>
        exact DirichletPositiveIndex_prepend_unary_closed unaryM positiveN

def DirichletSeriesConv (term : BHist -> BHist -> BHist) (s S : BHist) : Prop :=
  exists ps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
    (forall n : BHist, UnaryHistory n -> DirichletPartSum term s n (ps n)) /\
      ComplexLimit ps N S M

def DirichletClassifierSpec (term : BHist -> BHist -> BHist) (s S T : BHist) : Prop :=
  DirichletSeriesConv term s S ∧ hsame S T

theorem DirichletClassifierSpec_limit_transport {term : BHist -> BHist -> BHist}
    {s S T U : BHist} :
    DirichletClassifierSpec term s S T -> hsame T U ->
      exists ps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
        (forall n : BHist, UnaryHistory n -> DirichletPartSum term s n (ps n)) ∧
          ComplexLimit ps N U M ∧ DirichletClassifierSpec term s S U := by
  intro classified sameTU
  cases classified with
  | intro conv sameST =>
      cases conv with
      | intro ps convRest =>
          cases convRest with
          | intro N convRest =>
              cases convRest with
              | intro M data =>
                  have sameSU : hsame S U := hsame_trans sameST sameTU
                  exact Exists.intro ps
                    (Exists.intro N
                      (Exists.intro M
                        (And.intro data.left
                          (And.intro (ComplexLimit_hsame_transport sameSU data.right)
                            (And.intro
                              (Exists.intro ps
                                (Exists.intro N
                                  (Exists.intro M (And.intro data.left data.right))))
                              sameSU)))))

def DirichletSeriesClassifierSpec (term : BHist -> BHist -> BHist)
    (s S T : BHist) : Prop :=
  DirichletSeriesConv term s S ∧ DirichletSeriesConv term s T ∧ hsame S T

theorem DirichletSeriesClassifierSpec_limit_transport
    {term : BHist -> BHist -> BHist} {s S T witness : BHist} :
    UnaryHistory witness -> Cont S witness T -> hsame S T -> DirichletSeriesConv term s S ->
      DirichletSeriesClassifierSpec term s S T := by
  intro _witnessUnary _continuation sameST convergence
  cases convergence with
  | intro ps convergenceRest =>
      cases convergenceRest with
      | intro N convergenceRest =>
          cases convergenceRest with
          | intro M data =>
              have transported : DirichletSeriesConv term s T :=
                Exists.intro ps
                  (Exists.intro N
                    (Exists.intro M
                      (And.intro data.left
                        (ComplexLimit_hsame_transport sameST data.right))))
              exact And.intro
                (Exists.intro ps (Exists.intro N (Exists.intro M data)))
                (And.intro transported sameST)

def AbsConvAbscissa (term : BHist -> BHist -> BHist) (sigma : BHist) : Prop :=
  UnaryHistory sigma ∧ exists witness : BHist, UnaryHistory witness ∧
    forall {s S : BHist}, ComplexHistoryCarrier s -> DirichletSeriesConv term s S ->
      Cont sigma witness S -> ComplexHistoryCarrier S

def DirichletSourceSpec
    (term : BHist -> BHist -> BHist) (s sigma witness S : BHist) : Prop :=
  AbsConvAbscissa term sigma ∧ ComplexHistoryCarrier s ∧ DirichletSeriesConv term s S ∧
    UnaryHistory witness ∧ Cont sigma witness S

theorem AbsConvAbscissa_witness_result_carrier
    {term : BHist -> BHist -> BHist} {sigma s S : BHist} :
    AbsConvAbscissa term sigma -> ComplexHistoryCarrier s -> DirichletSeriesConv term s S ->
      exists witness : BHist, UnaryHistory witness ∧
        (Cont sigma witness S -> ComplexHistoryCarrier S) := by
  intro abscissa sourceCarrier convergence
  cases abscissa with
  | intro _sigmaUnary witnessRow =>
      cases witnessRow with
      | intro witness witnessData =>
          exact Exists.intro witness
            (And.intro witnessData.left
              (fun continuation =>
                have resultCarrier : ComplexHistoryCarrier S :=
                  witnessData.right sourceCarrier convergence continuation
                resultCarrier))

theorem DirichletSourceSpec_result_carrier
    {term : BHist -> BHist -> BHist} {s sigma witness S : BHist} :
    DirichletSourceSpec term s sigma witness S -> ComplexHistoryCarrier S := by
  intro source
  cases source.right.right.left with
  | intro ps convRest =>
      cases convRest with
      | intro N convRest =>
          cases convRest with
          | intro M convData =>
              exact convData.right.right.left

theorem DirichletSourceSpec_witness_result_carrier
    {term : BHist -> BHist -> BHist} {s sigma witness S : BHist} :
    DirichletSourceSpec term s sigma witness S ->
      ∃ witness : BHist, UnaryHistory witness ∧
        (Cont sigma witness S -> ComplexHistoryCarrier S) := by
  intro source
  exact AbsConvAbscissa_witness_result_carrier source.left source.right.left source.right.right.left

theorem dirichlet_semantic_name_certificate {term : BHist -> BHist -> BHist}
    {s S : BHist} :
    DirichletSeriesConv term s S ->
      SemanticNameCert (DirichletSeriesConv term s) (DirichletSeriesConv term s)
        (DirichletSeriesConv term s) hsame := by
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

theorem dirichlet_name_certificate {term : BHist -> BHist -> BHist} {s S : BHist}
    (conv : DirichletSeriesConv term s S) :
    NameCert (DirichletSeriesConv term s) hsame := by
  exact {
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
      | intro ps rest =>
          cases rest with
          | intro N rest =>
              cases rest with
              | intro M data =>
                  exact Exists.intro ps
                    (Exists.intro N
                      (Exists.intro M
                        (And.intro data.left
                          (ComplexLimit_hsame_transport same data.right))))
  }

end BEDC.Derived.DirichletSeriesUp
