import BEDC.Derived.DirichletSeriesUp

namespace BEDC.Derived.ZetaBasicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.DirichletSeriesUp

def ZetaBasicUnitTerm (_n s : BHist) : BHist := BHist.e1 s

def ZetaBasicPartSum (s n z : BHist) : Prop :=
  DirichletPartSum ZetaBasicUnitTerm s n z

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

end BEDC.Derived.ZetaBasicUp
