import BEDC.Derived.DirichletSeriesUp

namespace BEDC.Derived.ZetaBasicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.DirichletSeriesUp

def ZetaBasicUnitTerm (_n s : BHist) : BHist := BHist.e1 s

def ZetaBasicPartSum (s n z : BHist) : Prop :=
  DirichletPartSum ZetaBasicUnitTerm s n z

def ZetaBasic (s z : BHist) : Prop :=
  DirichletSeriesConv ZetaBasicUnitTerm s z

def ZetaBasicClassifierSpec (s z z' : BHist) : Prop :=
  ZetaBasic s z ∧ hsame z z'

def ZetaBasicSourceSpec (s : BHist) : Prop := UnaryHistory s

def ZetaBasicPatternSpec (s n z : BHist) : Prop :=
  UnaryHistory n ∧ ZetaBasicPartSum s n z ∧ hsame (ZetaBasicUnitTerm n s) (BHist.e1 s)

def ZetaBasicLedgerPolicy (s z : BHist) : Prop :=
  ZetaBasicSourceSpec s ∧ ZetaBasic s z ∧ ComplexHistoryCarrier z ∧
    exists n p : BHist, UnaryHistory n ∧ ZetaBasicPartSum s n p

theorem ZetaBasicSourceSpec_unit_term_carrier {s : BHist} :
    ZetaBasicSourceSpec s ->
      UnaryHistory (ZetaBasicUnitTerm BHist.Empty s) ∧
        (hsame (ZetaBasicUnitTerm BHist.Empty s) BHist.Empty -> False) := by
  intro source
  unfold ZetaBasicSourceSpec at source
  unfold ZetaBasicUnitTerm
  exact And.intro (unary_e1_closed source) not_hsame_e1_empty

theorem ZetaBasicPartSum_unary_result {s n z : BHist} :
    UnaryHistory s -> UnaryHistory n -> ZetaBasicPartSum s n z -> UnaryHistory z := by
  intro unaryS unaryN sum
  induction sum with
  | zero =>
      exact unary_empty
  | step previous stepCont ih =>
      have unaryPreviousIndex : UnaryHistory _ := unary_e1_inversion unaryN
      have unaryPreviousSum : UnaryHistory _ := ih unaryPreviousIndex
      have unaryTerm : UnaryHistory (BHist.e1 s) := unary_e1_closed unaryS
      exact unary_cont_closed unaryPreviousSum unaryTerm stepCont

theorem ZetaBasicPartSum_index_unary {s n z : BHist} :
    ZetaBasicPartSum s n z -> UnaryHistory n := by
  intro sum
  induction sum with
  | zero =>
      exact unary_empty
  | step _previous _stepCont ih =>
      exact unary_e1_closed ih

theorem ZetaBasicPartSum_successor_result_nonempty {s n z : BHist} :
    ZetaBasicPartSum s (BHist.e1 n) z -> (hsame z BHist.Empty -> False) := by
  intro sum sameEmpty
  cases sum with
  | step _previous stepCont =>
      have emptyStep : Cont _ (ZetaBasicUnitTerm n s) BHist.Empty :=
        cont_result_hsame_transport stepCont sameEmpty
      have endpoints := cont_empty_result_inversion emptyStep
      exact not_hsame_e1_empty endpoints.right

theorem ZetaBasicPartSum_successor_nonempty_name_certificate {s n z : BHist}
    (sum : ZetaBasicPartSum s (BHist.e1 n) z) :
    NameCert
      (fun result : BHist =>
        ZetaBasicPartSum s (BHist.e1 n) result ∧ (hsame result BHist.Empty -> False))
      hsame := by
  constructor
  · exact Exists.intro z
      (And.intro sum (ZetaBasicPartSum_successor_result_nonempty sum))
  · intro result _source
    exact hsame_refl result
  · intro result result' sameResult
    exact hsame_symm sameResult
  · intro result result' result'' sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro result result' sameResult source
    cases sameResult
    exact source

theorem ZetaBasicPartSum_positive_index_result_nonempty {s n z : BHist} :
    DirichletPositiveIndex n -> ZetaBasicPartSum s n z ->
      (hsame z BHist.Empty -> False) := by
  intro positive sum sameEmpty
  cases positive with
  | intro tail data =>
      cases data with
      | intro _unaryTail nEq =>
          cases nEq
          exact ZetaBasicPartSum_successor_result_nonempty sum sameEmpty

theorem ZetaBasicPartSum_successor_step_inversion {s n z : BHist} :
    ZetaBasicPartSum s (BHist.e1 n) z ->
      exists previous : BHist, ZetaBasicPartSum s n previous ∧ Cont previous (BHist.e1 s) z := by
  intro sum
  cases sum with
  | step previousSum stepCont =>
      unfold ZetaBasicUnitTerm at stepCont
      exact Exists.intro _ (And.intro previousSum stepCont)

theorem ZetaBasicClassifierSpec_successor_limit_transport {s z z' z'' n P Q : BHist} :
    ZetaBasicClassifierSpec s z z' -> hsame z' z'' -> ZetaBasicPartSum s n P ->
      Cont P (ZetaBasicUnitTerm n s) Q ->
        ((exists ps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
          (forall k : BHist, UnaryHistory k -> ZetaBasicPartSum s k (ps k)) ∧
            ComplexLimit ps N z'' M) ∧ ZetaBasicPartSum s (BHist.e1 n) Q ∧
              ZetaBasicClassifierSpec s z z'') := by
  intro classified sameZTarget partialSum stepCont
  cases classified with
  | intro basic sameZClassified =>
      cases basic with
      | intro ps basicRest =>
          cases basicRest with
          | intro N basicRest =>
              cases basicRest with
              | intro M data =>
                  have sameZTransported : hsame z z'' := hsame_trans sameZClassified sameZTarget
                  exact And.intro
                    (Exists.intro ps
                      (Exists.intro N
                        (Exists.intro M
                          (And.intro data.left
                            (ComplexLimit_hsame_transport sameZTransported data.right)))))
                    (And.intro (DirichletPartSum.step partialSum stepCont)
                      (And.intro
                        (Exists.intro ps
                          (Exists.intro N
                            (Exists.intro M (And.intro data.left data.right))))
                        sameZTransported))

theorem ZetaBasicPatternSpec_successor_step_inversion {s n z : BHist} :
    ZetaBasicPatternSpec s (BHist.e1 n) z ->
      ∃ previous : BHist, ZetaBasicPatternSpec s n previous ∧ Cont previous (BHist.e1 s) z := by
  intro pattern
  have step := ZetaBasicPartSum_successor_step_inversion pattern.right.left
  cases step with
  | intro previous previousData =>
      have unaryN : UnaryHistory n := unary_e1_inversion pattern.left
      exact Exists.intro previous
        (And.intro (And.intro unaryN (And.intro previousData.left (hsame_refl _)))
          previousData.right)

theorem ZetaBasicLedgerPolicy_carrier_fields {s z : BHist} :
    ZetaBasicLedgerPolicy s z ->
      ZetaBasicSourceSpec s ∧ ZetaBasic s z ∧ ComplexHistoryCarrier z := by
  intro ledger
  exact And.intro ledger.left (And.intro ledger.right.left ledger.right.right.left)

theorem ZetaBasicPartSum_empty_source_successor_result_shape {n z : BHist} :
    ZetaBasicPartSum BHist.Empty (BHist.e1 n) z ->
      exists previous : BHist,
        ZetaBasicPartSum BHist.Empty n previous ∧ hsame z (BHist.e1 previous) := by
  intro sum
  have inverted := ZetaBasicPartSum_successor_step_inversion sum
  cases inverted with
  | intro previous previousData =>
      exact Exists.intro previous
        (And.intro previousData.left
          (previousData.right.trans (congrArg BHist.e1 (append_empty_right previous))))

theorem ZetaBasicPartSum_successor_source_hsame_transport_step {s t n z : BHist} :
    hsame s t -> ZetaBasicPartSum s (BHist.e1 n) z ->
      exists previous transported : BHist, ZetaBasicPartSum t n previous ∧
        Cont previous (BHist.e1 t) transported ∧ hsame z transported := by
  intro sameST sum
  have inverted := ZetaBasicPartSum_successor_step_inversion sum
  cases inverted with
  | intro previous previousData =>
      have unaryN : UnaryHistory n := ZetaBasicPartSum_index_unary previousData.left
      have transportedPrevious :=
        DirichletPartSum_term_hsame_transport
          (term := ZetaBasicUnitTerm) (term' := ZetaBasicUnitTerm) (s := s) (s' := t)
          (fun {_m} _unaryM => hsame_e1_congr sameST)
          unaryN previousData.left
      cases transportedPrevious with
      | intro previous' transportData =>
          let transported := append previous' (BHist.e1 t)
          have transportedStep : Cont previous' (BHist.e1 t) transported := cont_intro rfl
          have sameResult : hsame z transported :=
            cont_respects_hsame transportData.right (hsame_e1_congr sameST)
              previousData.right transportedStep
          exact Exists.intro previous'
            (Exists.intro transported
              (And.intro transportData.left (And.intro transportedStep sameResult)))

theorem ZetaBasicPartSum_successor_source_hsame_previous_deterministic {s t n z u : BHist} :
    hsame s t -> ZetaBasicPartSum s (BHist.e1 n) z ->
      ZetaBasicPartSum t (BHist.e1 n) u ->
        exists p q : BHist, ZetaBasicPartSum s n p ∧ ZetaBasicPartSum t n q ∧
          hsame p q ∧ Cont p (BHist.e1 s) z ∧ Cont q (BHist.e1 t) u ∧ hsame z u := by
  intro sameST leftSum rightSum
  have leftStep := ZetaBasicPartSum_successor_step_inversion leftSum
  have rightStep := ZetaBasicPartSum_successor_step_inversion rightSum
  cases leftStep with
  | intro p pData =>
      cases rightStep with
      | intro q qData =>
          have unaryN : UnaryHistory n := ZetaBasicPartSum_index_unary pData.left
          have samePQ : hsame p q :=
            DirichletPartSum_term_hsame_transport_deterministic
              (term := ZetaBasicUnitTerm) (term' := ZetaBasicUnitTerm) (s := s) (s' := t)
              (fun {_m} _unaryM => hsame_e1_congr sameST)
              unaryN pData.left qData.left
          have sameZU : hsame z u :=
            cont_respects_hsame samePQ (hsame_e1_congr sameST) pData.right qData.right
          exact Exists.intro p
            (Exists.intro q
              (And.intro pData.left
                (And.intro qData.left
                  (And.intro samePQ
                    (And.intro pData.right (And.intro qData.right sameZU))))))

theorem ZetaBasicPartSum_successor_source_hsame_transport_result_nonempty {s t n z : BHist} :
    hsame s t -> ZetaBasicPartSum s (BHist.e1 n) z ->
      exists previous transported : BHist, ZetaBasicPartSum t n previous ∧
        Cont previous (BHist.e1 t) transported ∧ hsame z transported ∧
          (hsame transported BHist.Empty -> False) := by
  intro sameST sum
  have transportedStep :=
    ZetaBasicPartSum_successor_source_hsame_transport_step sameST sum
  cases transportedStep with
  | intro previous resultData =>
      cases resultData with
      | intro transported transportedData =>
          have transportedSum : ZetaBasicPartSum t (BHist.e1 n) transported :=
            DirichletPartSum.step transportedData.left transportedData.right.left
          exact Exists.intro previous
            (Exists.intro transported
              (And.intro transportedData.left
                (And.intro transportedData.right.left
                  (And.intro transportedData.right.right
                    (ZetaBasicPartSum_successor_result_nonempty transportedSum)))))

theorem ZetaBasicPartSum_successor_source_result_nonempty_transport {s t n z : BHist} :
    hsame s t -> ZetaBasicPartSum s (BHist.e1 n) z ->
      exists u : BHist, ZetaBasicPartSum t (BHist.e1 n) u ∧
        hsame z u ∧ (hsame u BHist.Empty -> False) := by
  intro sameST sum
  have transported := ZetaBasicPartSum_successor_source_hsame_transport_step sameST sum
  cases transported with
  | intro previous transportedData =>
      cases transportedData with
      | intro u stepData =>
          have targetSum : ZetaBasicPartSum t (BHist.e1 n) u :=
            DirichletPartSum.step stepData.left stepData.right.left
          exact Exists.intro u
            (And.intro targetSum
              (And.intro stepData.right.right
                (ZetaBasicPartSum_successor_result_nonempty targetSum)))

theorem ZetaBasicPatternSpec_successor_source_hsame_transport {s t n z : BHist} :
    hsame s t -> ZetaBasicPatternSpec s (BHist.e1 n) z ->
      exists u : BHist, ZetaBasicPatternSpec t (BHist.e1 n) u ∧ hsame z u ∧
        (hsame u BHist.Empty -> False) := by
  intro sameST pattern
  have transported :=
    ZetaBasicPartSum_successor_source_result_nonempty_transport sameST pattern.right.left
  cases transported with
  | intro u data =>
      exact Exists.intro u
        (And.intro
          (And.intro pattern.left
            (And.intro data.left (hsame_refl (ZetaBasicUnitTerm (BHist.e1 n) t))))
          (And.intro data.right.left data.right.right))

theorem ZetaBasic_semanticNameCert {s z : BHist} :
    ZetaBasic s z ->
      SemanticNameCert (ZetaBasic s) (ZetaBasic s) (ZetaBasic s) hsame := by
  intro basic
  exact {
    core := {
      carrier_inhabited := Exists.intro z basic
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
        cases source with
        | intro ps sourceRest =>
            cases sourceRest with
            | intro N sourceRest =>
                cases sourceRest with
                | intro M sourceData =>
                    exact Exists.intro ps
                      (Exists.intro N
                        (Exists.intro M
                          (And.intro sourceData.left
                            (ComplexLimit_hsame_transport sameResult sourceData.right))))
    }
    pattern_sound := by
      intro _result source
      exact source
    ledger_sound := by
      intro _result source
      exact source
  }

theorem zeta_basic_semantic_name_certificate {s n z : BHist}
    (sum : ZetaBasicPartSum s (BHist.e1 n) z) :
    SemanticNameCert
      (fun result : BHist =>
        ZetaBasicPartSum s (BHist.e1 n) result ∧ (hsame result BHist.Empty -> False))
      (fun result : BHist =>
        ZetaBasicPartSum s (BHist.e1 n) result ∧ (hsame result BHist.Empty -> False))
      (fun result : BHist =>
        ZetaBasicPartSum s (BHist.e1 n) result ∧ (hsame result BHist.Empty -> False))
      (fun result result' : BHist =>
        ZetaBasicPartSum s (BHist.e1 n) result ∧
          ZetaBasicPartSum s (BHist.e1 n) result' ∧ hsame result result') := by
  exact {
    core := {
      carrier_inhabited := Exists.intro z
        (And.intro sum (ZetaBasicPartSum_successor_result_nonempty sum))
      equiv_refl := by
        intro result source
        exact And.intro source.left (And.intro source.left (hsame_refl result))
      equiv_symm := by
        intro result result' classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro result result' result'' leftClass rightClass
        exact And.intro leftClass.left
          (And.intro rightClass.right.left
            (hsame_trans leftClass.right.right rightClass.right.right))
      carrier_respects_equiv := by
        intro result result' classified _source
        exact And.intro classified.right.left
          (ZetaBasicPartSum_successor_result_nonempty classified.right.left)
    }
    pattern_sound := by
      intro result source
      exact source
    ledger_sound := by
      intro result source
      exact source
  }

end BEDC.Derived.ZetaBasicUp
