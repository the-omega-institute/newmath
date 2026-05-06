import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.RealAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.ComplexSeriesUp

def RealAnalyticTrigPart (zero : BHist) (sinTerm cosTerm : BHist -> BHist)
    (n sinResult cosResult pairResult : BHist) : Prop :=
  ComplexPartSum zero sinTerm n sinResult ∧ ComplexPartSum zero cosTerm n cosResult ∧
    Cont sinResult cosResult pairResult

def RealAnalyticSinCosCandidate (x : BHist) (sinTerm cosTerm : BHist -> BHist)
    (n sinResult cosResult pairResult : BHist) : Prop :=
  ComplexHistoryCarrier x ∧ UnaryHistory n ∧
    RealAnalyticTrigPart x sinTerm cosTerm n sinResult cosResult pairResult

theorem RealAnalyticSinCosCandidate_pair_unary {x n sinResult cosResult pairResult : BHist}
    {sinTerm cosTerm : BHist -> BHist}
    (sinUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (sinTerm m))
    (cosUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (cosTerm m)) :
    RealAnalyticSinCosCandidate x sinTerm cosTerm n sinResult cosResult pairResult ->
      UnaryHistory sinResult ∧ UnaryHistory cosResult ∧ UnaryHistory pairResult := by
  intro candidate
  have xUnary : UnaryHistory x :=
    ComplexHistoryCarrier_unary candidate.left
  have sinResultUnary : UnaryHistory sinResult :=
    ComplexPartSum_result_unary xUnary sinUnary candidate.right.right.left
  have cosResultUnary : UnaryHistory cosResult :=
    ComplexPartSum_result_unary xUnary cosUnary candidate.right.right.right.left
  exact And.intro sinResultUnary
    (And.intro cosResultUnary
      (unary_cont_closed sinResultUnary cosResultUnary candidate.right.right.right.right))

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

theorem RealAnalyticLeibnizPartSum_successor_result_deterministic
    {term : BHist -> BHist} {n S T U : BHist} :
    RealAnalyticLeibnizPartSum term n S ->
      Cont S (term n) T ->
        RealAnalyticLeibnizPartSum term (BHist.e1 n) U ->
          hsame T U := by
  have deterministic :
      forall {n S T : BHist},
        RealAnalyticLeibnizPartSum term n S ->
          RealAnalyticLeibnizPartSum term n T ->
            hsame S T := by
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
            exact cont_respects_hsame samePartial (hsame_refl (term _)) leftStep rightStep
  intro source stepContinuation target
  cases target with
  | step targetPrevious targetContinuation =>
      have samePrevious := deterministic source targetPrevious
      exact cont_respects_hsame samePrevious (hsame_refl (term n)) stepContinuation
        targetContinuation

def RealAnalyticPiBoundary (term : BHist -> BHist) (candidate : BHist) : Prop :=
  exists n S : BHist,
    RealAnalyticLeibnizPartSum term n S ∧ Cont S BHist.Empty candidate ∧
      UnaryHistory candidate

def RealAnalyticPiLocalData (leibnizTerm : BHist -> BHist) (n sum pi : BHist) : Prop :=
  UnaryHistory n ∧ RealAnalyticLeibnizPartSum leibnizTerm n sum ∧ UnaryHistory sum ∧
    Cont sum sum pi

def RealAnalyticPiCandidate (leibnizTerm : BHist -> BHist) (limit : BHist) : Prop :=
  exists n S : BHist, RealAnalyticLeibnizPartSum leibnizTerm n S ∧ Cont S BHist.Empty limit

theorem RealAnalyticPiCandidate_empty_cont_readback {leibnizTerm : BHist -> BHist}
    {n S limit : BHist} :
    RealAnalyticLeibnizPartSum leibnizTerm n S -> Cont S BHist.Empty limit ->
      RealAnalyticPiCandidate leibnizTerm limit ∧ hsame S limit := by
  intro partSum limitCont
  exact
    And.intro
      (Exists.intro n (Exists.intro S (And.intro partSum limitCont)))
      (hsame_symm (cont_right_unit_iff.mp limitCont))

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

def RealAnalyticLog (x logValue : BHist) (bisect M : BHist -> BHist) : Prop :=
  ComplexHistoryCarrier x ∧
    ComplexLimit bisect (fun _ : BHist => BHist.Empty) logValue M ∧
      forall {n : BHist}, UnaryHistory n -> UnaryHistory (bisect n)

theorem RealAnalyticLog_hsame_transport_value_unary {x x' logValue logValue' : BHist}
    {bisect bisect' M : BHist -> BHist} :
    hsame x x' -> hsame logValue logValue' ->
      (forall {n : BHist}, UnaryHistory n -> hsame (bisect n) (bisect' n)) ->
        RealAnalyticLog x logValue bisect M ->
          RealAnalyticLog x' logValue' bisect' M ∧ UnaryHistory logValue' := by
  intro sameX sameLogValue sameBisect logData
  have xCarrier' : ComplexHistoryCarrier x' :=
    ComplexHistoryLedgerPolicy_visible_carrier (And.intro logData.left sameX)
  have limitBisect' : ComplexLimit bisect' (fun _ : BHist => BHist.Empty) logValue M :=
    ComplexLimit_sequence_hsame_transport sameBisect logData.right.left
  have limitValue' : ComplexLimit bisect' (fun _ : BHist => BHist.Empty) logValue' M :=
    ComplexLimit_hsame_transport sameLogValue limitBisect'
  have bisectUnary' : forall {n : BHist}, UnaryHistory n -> UnaryHistory (bisect' n) := by
    intro n unaryN
    exact unary_transport (logData.right.right unaryN) (sameBisect unaryN)
  exact And.intro
    (And.intro xCarrier' (And.intro limitValue' bisectUnary'))
    (ComplexHistoryCarrier_unary limitValue'.right.left)

theorem RealAnalyticSuppliedLimitConsumption_boundary {s t N M : BHist -> BHist}
    {r r' : BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) (t n)) ->
      hsame r r' -> ComplexLimit s N r M ->
        ComplexLimit t N r' M ∧ ComplexHistoryCarrier r' := by
  intro pointwise sameLimit limit
  have transportedSequence : ComplexLimit t N r M :=
    ComplexLimit_sequence_hsame_transport pointwise limit
  have transportedLimit : ComplexLimit t N r' M :=
    ComplexLimit_hsame_transport sameLimit transportedSequence
  exact And.intro transportedLimit transportedLimit.right.left

def RealAnalyticExp (x bound modulus y : BHist) : Prop :=
  ComplexHistoryCarrier x ∧ UnaryHistory bound ∧ UnaryHistory modulus ∧
    exists n S : BHist, UnaryHistory n ∧ RealAnalyticExpPart x n S ∧ Cont S modulus y

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

theorem RealAnalyticTrigPart_pair_index_result_unary
    {zero n sinResult cosResult pairResult : BHist} {sinTerm cosTerm : BHist -> BHist}
    (zeroUnary : UnaryHistory zero)
    (sinUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (sinTerm m))
    (cosUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (cosTerm m)) :
    RealAnalyticTrigPart zero sinTerm cosTerm n sinResult cosResult pairResult ->
      UnaryHistory n ∧ UnaryHistory sinResult ∧ UnaryHistory cosResult ∧
        UnaryHistory pairResult := by
  intro trigPart
  have sinIndexResult :=
    RealAnalyticComplexPartSum_index_result_unary zeroUnary sinUnary trigPart.left
  have cosIndexResult :=
    RealAnalyticComplexPartSum_index_result_unary zeroUnary cosUnary trigPart.right.left
  exact And.intro sinIndexResult.left
    (And.intro sinIndexResult.right
      (And.intro cosIndexResult.right
        (unary_cont_closed sinIndexResult.right cosIndexResult.right trigPart.right.right)))

theorem RealAnalyticSinAdd_local_product_sum_unary {zero n sx cx sy cy pairX pairY
    leftProd rightProd sum : BHist} {sinX cosX sinY cosY : BHist -> BHist}
    (zeroUnary : UnaryHistory zero)
    (sinXUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (sinX m))
    (cosXUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (cosX m))
    (sinYUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (sinY m))
    (cosYUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (cosY m)) :
    RealAnalyticTrigPart zero sinX cosX n sx cx pairX ->
      RealAnalyticTrigPart zero sinY cosY n sy cy pairY ->
        Cont sx cy leftProd -> Cont cx sy rightProd -> Cont leftProd rightProd sum ->
          UnaryHistory leftProd ∧ UnaryHistory rightProd ∧ UnaryHistory sum := by
  intro trigX trigY leftCont rightCont sumCont
  have trigXUnary :=
    RealAnalyticTrigPart_pair_index_result_unary zeroUnary sinXUnary cosXUnary trigX
  have trigYUnary :=
    RealAnalyticTrigPart_pair_index_result_unary zeroUnary sinYUnary cosYUnary trigY
  have leftProdUnary : UnaryHistory leftProd :=
    unary_cont_closed trigXUnary.right.left trigYUnary.right.right.left leftCont
  have rightProdUnary : UnaryHistory rightProd :=
    unary_cont_closed trigXUnary.right.right.left trigYUnary.right.left rightCont
  exact And.intro leftProdUnary
    (And.intro rightProdUnary
      (unary_cont_closed leftProdUnary rightProdUnary sumCont))

theorem RealAnalyticCosAdd_local_product_difference_unary {zero n sx cx sy cy pairX pairY
    leftProd rightProd diff : BHist} {sinX cosX sinY cosY : BHist -> BHist}
    (zeroUnary : UnaryHistory zero)
    (sinXUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (sinX m))
    (cosXUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (cosX m))
    (sinYUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (sinY m))
    (cosYUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (cosY m)) :
    RealAnalyticTrigPart zero sinX cosX n sx cx pairX ->
      RealAnalyticTrigPart zero sinY cosY n sy cy pairY ->
        Cont cx cy leftProd -> Cont sx sy rightProd -> Cont leftProd rightProd diff ->
          UnaryHistory leftProd ∧ UnaryHistory rightProd ∧ UnaryHistory diff := by
  intro trigX trigY leftCont rightCont diffCont
  have trigXUnary :=
    RealAnalyticTrigPart_pair_index_result_unary zeroUnary sinXUnary cosXUnary trigX
  have trigYUnary :=
    RealAnalyticTrigPart_pair_index_result_unary zeroUnary sinYUnary cosYUnary trigY
  have leftProdUnary : UnaryHistory leftProd :=
    unary_cont_closed trigXUnary.right.right.left trigYUnary.right.right.left leftCont
  have rightProdUnary : UnaryHistory rightProd :=
    unary_cont_closed trigXUnary.right.left trigYUnary.right.left rightCont
  exact And.intro leftProdUnary
    (And.intro rightProdUnary
      (unary_cont_closed leftProdUnary rightProdUnary diffCont))

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

theorem RealAnalyticPiBoundary_leibniz_index_result_unary {term : BHist -> BHist}
    {candidate : BHist}
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (term m)) :
    RealAnalyticPiBoundary term candidate ->
      exists n S : BHist, UnaryHistory n ∧ UnaryHistory S ∧ Cont S BHist.Empty candidate := by
  intro boundary
  have leibnizUnary :
      forall {n S : BHist}, RealAnalyticLeibnizPartSum term n S ->
        UnaryHistory n ∧ UnaryHistory S := by
    intro n S leibniz
    induction leibniz with
    | zero =>
        exact And.intro unary_empty unary_empty
    | step previous stepCont ih =>
        exact And.intro (unary_e1_closed ih.left)
          (unary_cont_closed ih.right (termUnary ih.left) stepCont)
  cases boundary with
  | intro n boundaryN =>
      cases boundaryN with
      | intro S data =>
          cases data with
          | intro leibniz rest =>
              have unaryPair : UnaryHistory n ∧ UnaryHistory S :=
                leibnizUnary leibniz
              exact Exists.intro n
                (Exists.intro S
                  (And.intro unaryPair.left
                    (And.intro unaryPair.right rest.left)))

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

theorem RealAnalyticRealCompletionDependencySurface_local_result_unary {zero result : BHist}
    {c modulus : BHist -> BHist} :
    UnaryHistory zero ->
      (forall {n : BHist}, UnaryHistory n -> UnaryHistory (c n)) ->
        (forall {n : BHist}, UnaryHistory n -> UnaryHistory (modulus n)) ->
          (exists n : BHist,
            ComplexPartSum zero c n result \/ ComplexAbsPartSum zero modulus n result) ->
            UnaryHistory result := by
  intro zeroUnary termUnary modulusUnary localSurface
  cases localSurface with
  | intro n surface =>
      cases surface with
      | inl partSum =>
          exact ComplexPartSum_result_unary zeroUnary termUnary partSum
      | inr absPartSum =>
          exact ComplexAbsPartSum_result_unary zeroUnary modulusUnary absPartSum

theorem RealAnalyticExp_local_witness_unary {x bound modulus y : BHist} :
    RealAnalyticExp x bound modulus y ->
      UnaryHistory bound ∧ UnaryHistory modulus ∧
        ∃ n S : BHist,
          UnaryHistory n ∧ UnaryHistory S ∧ RealAnalyticExpPart x n S ∧ Cont S modulus y := by
  intro exp
  cases exp.right.right.right with
  | intro n witnessN =>
      cases witnessN with
      | intro S data =>
          have xUnary : UnaryHistory x := ComplexHistoryCarrier_unary exp.left
          have termUnary :
              forall {m : BHist}, UnaryHistory m -> UnaryHistory (append x m) := by
            intro m unaryM
            exact unary_append_closed xUnary unaryM
          have sumUnary : UnaryHistory S :=
            ComplexPartSum_result_unary xUnary termUnary data.right.left.right.left
          exact And.intro exp.right.left
            (And.intro exp.right.right.left
              (Exists.intro n
                (Exists.intro S
                  (And.intro data.left
                    (And.intro sumUnary
                      (And.intro data.right.left data.right.right))))))

theorem RealAnalyticExp_product_witness_unary {x y bx bynd mx my ex ey prod : BHist} :
    RealAnalyticExp x bx mx ex -> RealAnalyticExp y bynd my ey -> Cont ex ey prod ->
      UnaryHistory ex ∧ UnaryHistory ey ∧ UnaryHistory prod := by
  intro expX expY product
  have xWitness := RealAnalyticExp_local_witness_unary expX
  have yWitness := RealAnalyticExp_local_witness_unary expY
  cases xWitness.right.right with
  | intro nx xData =>
      cases xData with
      | intro sx xLocal =>
          cases yWitness.right.right with
          | intro ny yData =>
              cases yData with
              | intro sy yLocal =>
                  have exUnary : UnaryHistory ex :=
                    unary_cont_closed xLocal.right.left xWitness.right.left
                      xLocal.right.right.right
                  have eyUnary : UnaryHistory ey :=
                    unary_cont_closed yLocal.right.left yWitness.right.left
                      yLocal.right.right.right
                  exact And.intro exUnary (And.intro eyUnary
                    (unary_cont_closed exUnary eyUnary product))

theorem RealAnalyticLogExpInverse_supplied_boundary_unary {x y e bound modulus : BHist}
    {bisect M : BHist -> BHist} :
    RealAnalyticLog x y bisect M -> RealAnalyticExp y bound modulus e -> hsame e x ->
      UnaryHistory e ∧ UnaryHistory x ∧ UnaryHistory y := by
  intro logData expData sameEX
  have expWitness := RealAnalyticExp_local_witness_unary expData
  have yUnary : UnaryHistory y :=
    ComplexHistoryCarrier_unary logData.right.left.right.left
  cases expWitness.right.right with
  | intro _n witnessN =>
      cases witnessN with
      | intro _S localData =>
        have eUnary : UnaryHistory e :=
          unary_cont_closed localData.right.left expWitness.right.left localData.right.right.right
        have xUnary : UnaryHistory x :=
          unary_transport eUnary sameEX
        exact And.intro eUnary (And.intro xUnary yUnary)

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
