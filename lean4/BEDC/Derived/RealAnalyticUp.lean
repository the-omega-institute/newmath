import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.RealAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexSeriesUp

def RealAnalyticTrigPart (zero : BHist) (sinTerm cosTerm : BHist -> BHist)
    (n sinResult cosResult pairResult : BHist) : Prop :=
  ComplexPartSum zero sinTerm n sinResult ∧ ComplexPartSum zero cosTerm n cosResult ∧
    Cont sinResult cosResult pairResult

def RealAnalyticLeibnizPartialSum (leibnizTerm : BHist -> BHist) (n S : BHist) :
    Prop :=
  UnaryHistory n ∧ ComplexPartSum BHist.Empty leibnizTerm n S ∧ UnaryHistory S

def RealAnalyticPi (leibnizTerm : BHist -> BHist) (pi : BHist) : Prop :=
  ∃ S : BHist,
    RealAnalyticLeibnizPartialSum leibnizTerm (BHist.e1 (BHist.e1 BHist.Empty)) S ∧
      hsame pi (append S S) ∧ UnaryHistory pi

inductive RealAnalyticLeibnizPartSum (term : BHist -> BHist) : BHist -> BHist -> Prop where
  | zero : RealAnalyticLeibnizPartSum term BHist.Empty BHist.Empty
  | step {n S T : BHist} :
      RealAnalyticLeibnizPartSum term n S -> Cont S (term n) T ->
        RealAnalyticLeibnizPartSum term (BHist.e1 n) T

theorem RealAnalyticLeibnizPartSum_pointwise_hsame_deterministic
    {term term' : BHist -> BHist} {n S T : BHist} :
    (forall {m : BHist}, UnaryHistory m -> hsame (term m) (term' m)) ->
      RealAnalyticLeibnizPartSum term n S ->
        RealAnalyticLeibnizPartSum term' n T -> hsame S T := by
  intro termSame source
  have indexUnary :
      forall {m P : BHist}, RealAnalyticLeibnizPartSum term m P -> UnaryHistory m := by
    intro m P sum
    induction sum with
    | zero =>
        exact unary_empty
    | step _ _ ih =>
        exact unary_e1_closed ih
  induction source generalizing T with
  | zero =>
      intro target
      cases target with
      | zero =>
          exact hsame_refl BHist.Empty
  | step previous stepContinuation ih =>
      intro target
      cases target with
      | step previous' stepContinuation' =>
          have unaryPrevious : UnaryHistory _ := indexUnary previous
          have samePrevious : hsame _ _ := ih previous'
          exact cont_respects_hsame samePrevious (termSame unaryPrevious)
            stepContinuation stepContinuation'

theorem RealAnalyticLeibnizPartSum_index_result_unary {term : BHist -> BHist}
    {n S : BHist}
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (term m)) :
    RealAnalyticLeibnizPartSum term n S -> UnaryHistory n ∧ UnaryHistory S := by
  intro sum
  induction sum with
  | zero =>
      exact And.intro unary_empty unary_empty
  | step previous stepContinuation ih =>
      exact And.intro (unary_e1_closed ih.left)
        (unary_cont_closed ih.right (termUnary ih.left) stepContinuation)

def RealAnalyticExpPart (x n S : BHist) : Prop :=
  ComplexHistoryCarrier x ∧
    ComplexPartSum x (fun m : BHist => append x m) n S ∧ UnaryHistory n

theorem RealAnalyticComplexPartSum_index_unary {zero : BHist} {c : BHist -> BHist}
    {n S : BHist} :
    ComplexPartSum zero c n S -> UnaryHistory n := by
  intro sum
  induction sum with
  | zero =>
      exact unary_empty
  | step _ _ ih =>
      exact unary_e1_closed ih

theorem RealAnalyticComplexPartSum_pointwise_result_unary_transport {zero zero' : BHist}
    {c d : BHist -> BHist} {n S T : BHist}
    (zeroUnary : UnaryHistory zero)
    (sameZero : hsame zero zero')
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (c m))
    (termSame : forall {m : BHist}, UnaryHistory m -> hsame (c m) (d m)) :
    UnaryHistory n -> ComplexPartSum zero c n S -> ComplexPartSum zero' d n T ->
      UnaryHistory T := by
  intro unaryN source target
  have sourceUnary : UnaryHistory S :=
    ComplexPartSum_result_unary zeroUnary termUnary source
  have sameResult : hsame S T :=
    ComplexPartSum_pointwise_hsame_deterministic sameZero termSame unaryN source target
  exact unary_transport sourceUnary sameResult

theorem RealAnalyticComplexAbsPartSum_pointwise_result_unary_transport {zero zero' : BHist}
    {modulus modulus' : BHist -> BHist} {n M T : BHist}
    (zeroUnary : UnaryHistory zero)
    (sameZero : hsame zero zero')
    (modulusUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (modulus m))
    (modulusSame : forall {m : BHist}, UnaryHistory m -> hsame (modulus m) (modulus' m)) :
    UnaryHistory n -> ComplexAbsPartSum zero modulus n M ->
      ComplexAbsPartSum zero' modulus' n T -> UnaryHistory T := by
  intro unaryN source target
  have sourceUnary : UnaryHistory M :=
    ComplexAbsPartSum_result_unary zeroUnary modulusUnary source
  have sameResult : hsame M T :=
    ComplexAbsPartSum_pointwise_hsame_deterministic sameZero modulusSame unaryN source target
  exact unary_transport sourceUnary sameResult

theorem RealAnalyticComplexPartSum_index_result_unary {zero : BHist} {c : BHist -> BHist}
    {n S : BHist}
    (zeroUnary : UnaryHistory zero)
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (c m)) :
    ComplexPartSum zero c n S -> UnaryHistory n ∧ UnaryHistory S := by
  intro sum
  induction sum with
  | zero =>
      exact And.intro unary_empty zeroUnary
  | step previous stepContinuation ih =>
      exact And.intro (unary_e1_closed ih.left)
        (unary_cont_closed ih.right (termUnary ih.left) stepContinuation)

theorem RealAnalyticComplexPartSum_closed_pointwise_index_result_unary_transport {zero zero' : BHist}
    {c d : BHist -> BHist} {n S T : BHist}
    (zeroUnary : UnaryHistory zero)
    (sameZero : hsame zero zero')
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (c m))
    (termSame : forall {m : BHist}, UnaryHistory m -> hsame (c m) (d m)) :
    ComplexPartSum zero c n S -> ComplexPartSum zero' d n T ->
      UnaryHistory n ∧ UnaryHistory T := by
  intro source target
  have unaryN : UnaryHistory n :=
    RealAnalyticComplexPartSum_index_unary source
  have unaryT : UnaryHistory T :=
    RealAnalyticComplexPartSum_pointwise_result_unary_transport zeroUnary sameZero
      termUnary termSame unaryN source target
  exact And.intro unaryN unaryT

theorem RealAnalyticComplexAbsPartSum_index_result_unary {zero : BHist}
    {modulus : BHist -> BHist} {n M : BHist}
    (zeroUnary : UnaryHistory zero)
    (modulusUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (modulus m)) :
    ComplexAbsPartSum zero modulus n M -> UnaryHistory n ∧ UnaryHistory M := by
  intro sum
  induction sum with
  | zero =>
      exact And.intro unary_empty zeroUnary
  | step previous stepContinuation ih =>
      exact And.intro (unary_e1_closed ih.left)
        (unary_cont_closed ih.right (modulusUnary ih.left) stepContinuation)

theorem RealAnalyticComplexAbsPartSum_closed_pointwise_index_result_unary_transport
    {zero zero' : BHist} {modulus modulus' : BHist -> BHist} {n M T : BHist}
    (zeroUnary : UnaryHistory zero)
    (sameZero : hsame zero zero')
    (modulusUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (modulus m))
    (modulusSame : forall {m : BHist}, UnaryHistory m -> hsame (modulus m) (modulus' m)) :
    ComplexAbsPartSum zero modulus n M -> ComplexAbsPartSum zero' modulus' n T ->
      UnaryHistory n ∧ UnaryHistory T := by
  intro source target
  have unaryN : UnaryHistory n :=
    (RealAnalyticComplexAbsPartSum_index_result_unary zeroUnary modulusUnary source).left
  have unaryT : UnaryHistory T :=
    RealAnalyticComplexAbsPartSum_pointwise_result_unary_transport zeroUnary sameZero
      modulusUnary modulusSame unaryN source target
  exact And.intro unaryN unaryT

theorem RealAnalyticLocalStream_obligations_package {zero zero' : BHist}
    {c d modulus modulus' : BHist -> BHist} :
    UnaryHistory zero -> hsame zero zero' ->
      (forall {i : BHist}, UnaryHistory i -> UnaryHistory (c i)) ->
        (forall {i : BHist}, UnaryHistory i -> UnaryHistory (modulus i)) ->
          (forall {i : BHist}, UnaryHistory i -> hsame (c i) (d i)) ->
            (forall {i : BHist}, UnaryHistory i -> hsame (modulus i) (modulus' i)) ->
              ((forall {n S : BHist}, ComplexPartSum zero c n S ->
                    UnaryHistory n ∧ UnaryHistory S) ∧
                (forall {n S T : BHist}, UnaryHistory n -> ComplexPartSum zero c n S ->
                  ComplexPartSum zero' d n T -> UnaryHistory T) ∧
                (forall {n M : BHist}, ComplexAbsPartSum zero modulus n M ->
                  UnaryHistory n ∧ UnaryHistory M) ∧
                (forall {n M T : BHist}, UnaryHistory n ->
                  ComplexAbsPartSum zero modulus n M ->
                    ComplexAbsPartSum zero' modulus' n T -> UnaryHistory T)) := by
  intro zeroUnary sameZero termUnary modulusUnary termSame modulusSame
  constructor
  · intro n S sum
    exact RealAnalyticComplexPartSum_index_result_unary zeroUnary termUnary sum
  constructor
  · intro n S T unaryN source target
    exact RealAnalyticComplexPartSum_pointwise_result_unary_transport zeroUnary sameZero
      termUnary termSame unaryN source target
  constructor
  · intro n M sum
    exact RealAnalyticComplexAbsPartSum_index_result_unary zeroUnary modulusUnary sum
  · intro n M T unaryN source target
    exact RealAnalyticComplexAbsPartSum_pointwise_result_unary_transport zeroUnary sameZero
      modulusUnary modulusSame unaryN source target

theorem real_analytic_certificate_boundary {zero : BHist} {c modulus : BHist -> BHist} :
    SemanticNameCert
      (fun result : BHist =>
        exists n : BHist,
          ComplexPartSum zero c n result \/ ComplexAbsPartSum zero modulus n result)
      (fun result : BHist =>
        exists n : BHist,
          ComplexPartSum zero c n result \/ ComplexAbsPartSum zero modulus n result)
      (fun result : BHist =>
        exists n : BHist,
          ComplexPartSum zero c n result \/ ComplexAbsPartSum zero modulus n result)
      hsame := by
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro zero
          (Exists.intro BHist.Empty (Or.inl ComplexPartSum.zero))
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

end BEDC.Derived.RealAnalyticUp
