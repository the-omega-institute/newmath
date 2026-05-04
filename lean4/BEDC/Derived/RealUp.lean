import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.StreamNameUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.RealUp.PrefixTruncation
import BEDC.Derived.RealUp.ConstantStreamBridge
import BEDC.Derived.RealUp.ConstantStream
import BEDC.Derived.RealUp.StreamReadback
import BEDC.Derived.RealUp.Readback

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RealIndependentReindexedConstant_rational_embedding_certificate {d e : BHist}
    {r q : BHist -> BHist} :
    ((RatHistoryCarrier d ↔
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n))) ∧
      (RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ↔
        RealConstantHistoryCarrier (BHist.e1 d))) ∧
      ((RatHistoryCarrier e ↔
        RatStreamNameCarrier (fun n : BHist => RatConstStream e (q n))) ∧
        (RatStreamNameCarrier (fun n : BHist => RatConstStream e (q n)) ↔
          RealConstantHistoryCarrier (BHist.e1 e))) ∧
        ((RatHistoryClassifier d e ↔
          RatStreamNameClassifier
            (fun n : BHist => RatConstStream d (r n))
            (fun n : BHist => RatConstStream e (q n))) ∧
          (RatStreamNameClassifier
            (fun n : BHist => RatConstStream d (r n))
            (fun n : BHist => RatConstStream e (q n)) ↔
              RealUnaryStreamClassifier
                (fun n : BHist => RatConstStream d (r n))
                (fun n : BHist => RatConstStream e (q n))) ∧
            (RealUnaryStreamClassifier
              (fun n : BHist => RatConstStream d (r n))
              (fun n : BHist => RatConstStream e (q n)) ↔
                RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e))) := by
  have leftCarrier :=
    RealConstantStreamCarrier_reindexed_streamName_bridge (d := d) (r := r)
  have rightCarrier :=
    RealConstantStreamCarrier_reindexed_streamName_bridge (d := e) (r := q)
  have streamClassifierIff :
      RatHistoryClassifier d e ↔
        RatStreamNameClassifier
          (fun n : BHist => RatConstStream d (r n))
          (fun n : BHist => RatConstStream e (q n)) := by
    constructor
    · intro ratClassifier
      constructor
      · exact Iff.mp leftCarrier.left ratClassifier.left
      · constructor
        · exact Iff.mp rightCarrier.left ratClassifier.right.left
        · intro n _nUnary
          change RatHistoryClassifier d e
          exact ratClassifier
    · intro streamClassifier
      have atEmpty := streamClassifier.right.right BHist.Empty unary_empty
      change RatHistoryClassifier d e at atEmpty
      exact atEmpty
  have streamUnaryIff :
      RatStreamNameClassifier
        (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n)) ↔
          RealUnaryStreamClassifier
            (fun n : BHist => RatConstStream d (r n))
            (fun n : BHist => RatConstStream e (q n)) := by
    constructor
    · intro streamClassifier
      exact streamClassifier.right.right
    · intro unaryClassifier
      constructor
      · intro n nUnary
        exact (unaryClassifier n nUnary).left
      · constructor
        · intro n nUnary
          exact (unaryClassifier n nUnary).right.left
        · exact unaryClassifier
  have unaryRealIff :
      RealUnaryStreamClassifier
        (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n)) ↔
          RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e) := by
    constructor
    · intro unaryClassifier
      have atEmpty := unaryClassifier BHist.Empty unary_empty
      change RatHistoryClassifier d e at atEmpty
      exact Iff.mpr RealConstantHistoryClassifier_e1_iff_rat atEmpty
    · intro realClassifier n _nUnary
      have ratClassifier : RatHistoryClassifier d e :=
        Iff.mp RealConstantHistoryClassifier_e1_iff_rat realClassifier
      change RatHistoryClassifier d e
      exact ratClassifier
  exact And.intro leftCarrier
    (And.intro rightCarrier
      (And.intro streamClassifierIff (And.intro streamUnaryIff unaryRealIff)))

theorem RealStreamClassifier_unary_denominator_context_closed
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} :
    RealStreamClassifier x y ->
    (forall n : Nat, UnaryHistory (pX n)) ->
    (forall n : Nat, UnaryHistory (tX n)) ->
    (forall n : Nat, hsame (pX n) (pY n)) ->
    (forall n : Nat, hsame (tX n) (tY n)) ->
    (forall n : Nat, Cont (pX n) (x n) (mX n)) ->
    (forall n : Nat, Cont (mX n) (tX n) (oX n)) ->
    (forall n : Nat, Cont (pY n) (y n) (mY n)) ->
    (forall n : Nat, Cont (mY n) (tY n) (oY n)) ->
    RealStreamClassifier oX oY := by
  intro classified prefXUnary tailXUnary prefSame tailSame prefXCont outXCont prefYCont
    outYCont n
  have contextClassifier :
      RatHistoryClassifier (append (pX n) (append (x n) (tX n)))
        (append (pY n) (append (y n) (tY n))) :=
    RatHistoryClassifier_unary_denominator_context_closed (classified n)
      (prefXUnary n) (prefSame n) (tailXUnary n) (tailSame n)
  have sameOutX : hsame (append (pX n) (append (x n) (tX n))) (oX n) := by
    have prefEq : mX n = append (pX n) (x n) := cont_iff_append.mp (prefXCont n)
    have outEq : oX n = append (mX n) (tX n) := cont_iff_append.mp (outXCont n)
    exact (append_assoc (pX n) (x n) (tX n)).symm.trans
      ((congrArg (fun h => append h (tX n)) prefEq).symm.trans outEq.symm)
  have sameOutY : hsame (append (pY n) (append (y n) (tY n))) (oY n) := by
    have prefEq : mY n = append (pY n) (y n) := cont_iff_append.mp (prefYCont n)
    have outEq : oY n = append (mY n) (tY n) := cont_iff_append.mp (outYCont n)
    exact (append_assoc (pY n) (y n) (tY n)).symm.trans
      ((congrArg (fun h => append h (tY n)) prefEq).symm.trans outEq.symm)
  exact RatHistoryClassifier_hsame_transport sameOutX sameOutY contextClassifier

theorem RealConstantHistoryClassifier_append_common_tail_cancel {d e tail : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append d tail)) (BHist.e1 (append e tail)) ->
      hsame d e := by
  intro classified
  have rational :
      RatHistoryClassifier (append d tail) (append e tail) :=
    Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
  exact append_right_cancel (k := tail) rational.right.right

theorem RealConstantStream_independent_reindexed_streamName_bridge {d e : BHist}
    {r q : BHist -> BHist} :
    (RatHistoryClassifier d e ↔
      RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n))) ∧
      (RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n)) ↔
          RealUnaryStreamClassifier (fun n : BHist => RatConstStream d (r n))
            (fun n : BHist => RatConstStream e (q n))) ∧
        (RealUnaryStreamClassifier (fun n : BHist => RatConstStream d (r n))
          (fun n : BHist => RatConstStream e (q n)) ↔
            RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e)) := by
  have carrierD :
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ↔
        RatHistoryCarrier d :=
    (RealConstantStreamCarrier_reindexed_streamName_bridge (d := d) (r := r)).left.symm
  have carrierE :
      RatStreamNameCarrier (fun n : BHist => RatConstStream e (q n)) ↔
        RatHistoryCarrier e :=
    (RealConstantStreamCarrier_reindexed_streamName_bridge (d := e) (r := q)).left.symm
  have streamClassifierIff :
      RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n)) ↔ RatHistoryClassifier d e := by
    constructor
    · intro streamClassifier
      have atEmpty := streamClassifier.right.right BHist.Empty unary_empty
      cases hR : r BHist.Empty with
      | Empty =>
          cases hQ : q BHist.Empty with
          | Empty =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
          | e0 _ =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
          | e1 _ =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
      | e0 _ =>
          cases hQ : q BHist.Empty with
          | Empty =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
          | e0 _ =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
          | e1 _ =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
      | e1 _ =>
          cases hQ : q BHist.Empty with
          | Empty =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
          | e0 _ =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
          | e1 _ =>
              simp only [RatConstStream] at atEmpty
              exact atEmpty
    · intro ratClassifier
      exact And.intro (Iff.mpr carrierD ratClassifier.left)
        (And.intro (Iff.mpr carrierE ratClassifier.right.left)
          (fun n _nUnary => by
            cases hR : r n with
            | Empty =>
                cases hQ : q n with
                | Empty =>
                    simp only [RatConstStream]
                    exact ratClassifier
                | e0 _ =>
                    simp only [RatConstStream]
                    exact ratClassifier
                | e1 _ =>
                    simp only [RatConstStream]
                    exact ratClassifier
            | e0 _ =>
                cases hQ : q n with
                | Empty =>
                    simp only [RatConstStream]
                    exact ratClassifier
                | e0 _ =>
                    simp only [RatConstStream]
                    exact ratClassifier
                | e1 _ =>
                    simp only [RatConstStream]
                    exact ratClassifier
            | e1 _ =>
                cases hQ : q n with
                | Empty =>
                    simp only [RatConstStream]
                    exact ratClassifier
                | e0 _ =>
                    simp only [RatConstStream]
                    exact ratClassifier
                | e1 _ =>
                    simp only [RatConstStream]
                    exact ratClassifier))
  have ratStreamIff :
      RatHistoryClassifier d e ↔
        RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
          (fun n : BHist => RatConstStream e (q n)) := by
    constructor
    · intro ratClassifier
      exact Iff.mpr streamClassifierIff ratClassifier
    · intro streamClassifier
      exact Iff.mp streamClassifierIff streamClassifier
  have streamUnaryIff :
      RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n)) ↔
          RealUnaryStreamClassifier (fun n : BHist => RatConstStream d (r n))
            (fun n : BHist => RatConstStream e (q n)) := by
    constructor
    · intro streamClassifier
      exact streamClassifier.right.right
    · intro unaryClassifier
      have ratClassifier : RatHistoryClassifier d e := by
        have atEmpty := unaryClassifier BHist.Empty unary_empty
        cases hR : r BHist.Empty with
        | Empty =>
            cases hQ : q BHist.Empty with
            | Empty =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e0 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e1 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
        | e0 _ =>
            cases hQ : q BHist.Empty with
            | Empty =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e0 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e1 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
        | e1 _ =>
            cases hQ : q BHist.Empty with
            | Empty =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e0 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e1 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
      exact And.intro (Iff.mpr carrierD ratClassifier.left)
        (And.intro (Iff.mpr carrierE ratClassifier.right.left) unaryClassifier)
  have unaryRealIff :
      RealUnaryStreamClassifier (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n)) ↔
          RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e) := by
    constructor
    · intro unaryClassifier
      have ratClassifier : RatHistoryClassifier d e := by
        have atEmpty := unaryClassifier BHist.Empty unary_empty
        cases hR : r BHist.Empty with
        | Empty =>
            cases hQ : q BHist.Empty with
            | Empty =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e0 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e1 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
        | e0 _ =>
            cases hQ : q BHist.Empty with
            | Empty =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e0 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e1 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
        | e1 _ =>
            cases hQ : q BHist.Empty with
            | Empty =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e0 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
            | e1 _ =>
                simp only [RatConstStream] at atEmpty
                exact atEmpty
      exact Iff.mpr RealConstantHistoryClassifier_e1_iff_rat ratClassifier
    · intro realClassifier n _nUnary
      have ratClassifier : RatHistoryClassifier d e :=
        Iff.mp RealConstantHistoryClassifier_e1_iff_rat realClassifier
      cases hR : r n with
      | Empty =>
          cases hQ : q n with
          | Empty =>
              simp only [RatConstStream]
              exact ratClassifier
          | e0 _ =>
              simp only [RatConstStream]
              exact ratClassifier
          | e1 _ =>
              simp only [RatConstStream]
              exact ratClassifier
      | e0 _ =>
          cases hQ : q n with
          | Empty =>
              simp only [RatConstStream]
              exact ratClassifier
          | e0 _ =>
              simp only [RatConstStream]
              exact ratClassifier
          | e1 _ =>
              simp only [RatConstStream]
              exact ratClassifier
      | e1 _ =>
          cases hQ : q n with
          | Empty =>
              simp only [RatConstStream]
              exact ratClassifier
          | e0 _ =>
              simp only [RatConstStream]
              exact ratClassifier
          | e1 _ =>
              simp only [RatConstStream]
              exact ratClassifier
  exact And.intro ratStreamIff (And.intro streamUnaryIff unaryRealIff)

theorem RealStreamClassifier_unary_denominator_context_selected_e1_pair_readback
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat} {a b : BHist} :
    RealStreamClassifier x y ->
      (forall i : Nat, UnaryHistory (pX i)) ->
        (forall i : Nat, UnaryHistory (tX i)) ->
          (forall i : Nat, hsame (pX i) (pY i)) ->
            (forall i : Nat, hsame (tX i) (tY i)) ->
              (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
                (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                  (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                    (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                      hsame (oX n) (BHist.e1 a) -> hsame (oY n) (BHist.e1 b) ->
                        UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified prefixX tailX samePrefix sameTail contPX contOX contPY contOY sameLeft
    sameRight
  have contextClassified : RealStreamClassifier oX oY :=
    RealStreamClassifier_unary_denominator_context_closed classified prefixX tailX samePrefix
      sameTail contPX contOX contPY contOY
  exact RealStreamClassifier_selected_e1_pair_readback contextClassified sameLeft sameRight

theorem RealStreamClassifier_unary_context_closed
    {x y prefX prefY tailX tailY : Nat -> BHist} :
    (forall i : Nat, UnaryHistory (prefX i)) ->
      (forall i : Nat, hsame (prefX i) (prefY i)) ->
        (forall i : Nat, UnaryHistory (tailX i)) ->
          (forall i : Nat, hsame (tailX i) (tailY i)) ->
            RealStreamClassifier x y ->
              RealStreamClassifier
                (fun i => append (prefX i) (append (x i) (tailX i)))
                (fun i => append (prefY i) (append (y i) (tailY i))) := by
  intro prefUnary prefSame tailUnary tailSame classified i
  exact RatHistoryClassifier_unary_denominator_context_closed (classified i)
    (prefUnary i) (prefSame i) (tailUnary i) (tailSame i)

theorem RealStreamClassifier_unary_denominator_context_e1_pair_readback
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat} {a b : BHist} :
    RealStreamClassifier x y -> (forall i : Nat, UnaryHistory (pX i)) ->
      (forall i : Nat, UnaryHistory (tX i)) ->
        (forall i : Nat, hsame (pX i) (pY i)) ->
          (forall i : Nat, hsame (tX i) (tY i)) ->
            (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
              (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                  (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                    hsame (oX n) (BHist.e1 a) -> hsame (oY n) (BHist.e1 b) ->
                      UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified prefixX tailX samePrefix sameTail contPX contOX contPY contOY sameX sameY
  have contextClassified : RealStreamClassifier oX oY :=
    RealStreamClassifier_unary_denominator_context_closed classified prefixX tailX samePrefix
      sameTail contPX contOX contPY contOY
  exact RealStreamClassifier_selected_e1_pair_readback contextClassified sameX sameY

theorem RealStreamClassifier_unary_denominator_context_selected_shape_package
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat} {zx zy : BHist} :
    RealStreamClassifier x y -> (forall i : Nat, UnaryHistory (pX i)) ->
      (forall i : Nat, UnaryHistory (tX i)) ->
        (forall i : Nat, hsame (pX i) (pY i)) ->
          (forall i : Nat, hsame (tX i) (tY i)) ->
            (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
              (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                  (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                    UnaryHistory (oX n) ∧ UnaryHistory (oY n) ∧
                      (hsame (oX n) BHist.Empty -> False) ∧
                        (hsame (oY n) BHist.Empty -> False) ∧
                          (hsame (oX n) (BHist.e0 zx) -> False) ∧
                            (hsame (oY n) (BHist.e0 zy) -> False) := by
  intro classified prefixX tailX samePrefix sameTail contPX contOX contPY contOY
  have contextClassified : RealStreamClassifier oX oY :=
    RealStreamClassifier_unary_denominator_context_closed classified prefixX tailX samePrefix
      sameTail contPX contOX contPY contOY
  have positives := RatHistoryClassifier_positive_denominators (contextClassified n)
  have leftRows := PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows := PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact And.intro leftRows.left
    (And.intro rightRows.left
      (And.intro leftRows.right
        (And.intro rightRows.right
          (And.intro
            (fun sameZero =>
              PositiveUnaryDenominator_e0_absurd
                (PositiveUnaryDenominator_hsame_transport sameZero positives.left))
            (fun sameZero =>
              PositiveUnaryDenominator_e0_absurd
                (PositiveUnaryDenominator_hsame_transport sameZero positives.right))))))

theorem RealStreamClassifier_selected_continuation_e1_pair_readback
    {x y : Nat -> BHist} {n : Nat} {q xq yq a b : BHist} :
    RealStreamClassifier x y -> UnaryHistory q -> Cont (x n) q xq -> Cont (y n) q yq ->
      hsame xq (BHist.e1 a) -> hsame yq (BHist.e1 b) ->
        UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified qUnary contX contY sameX sameY
  have pointClassified : RatHistoryClassifier (x n) (y n) := classified n
  have continued :
      RatHistoryClassifier (append (x n) q) (append (y n) q) :=
    RatHistoryClassifier_append_unary_denominator_closed pointClassified qUnary
      (hsame_refl q)
  have transported : RatHistoryClassifier xq yq :=
    RatHistoryClassifier_hsame_transport contX.symm contY.symm continued
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameX sameY transported
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RealStreamClassifier_selected_positive_unary_nonempty_package {x y : Nat -> BHist}
    {n : Nat} :
    RealStreamClassifier x y ->
      PositiveUnaryDenominator (x n) ∧ PositiveUnaryDenominator (y n) ∧
        UnaryHistory (x n) ∧ UnaryHistory (y n) ∧
          (hsame (x n) BHist.Empty -> False) ∧
            (hsame (y n) BHist.Empty -> False) := by
  intro classified
  have positiveEndpoints := RatHistoryClassifier_positive_denominators (classified n)
  have xData := PositiveUnaryDenominator_unary_and_nonempty positiveEndpoints.left
  have yData := PositiveUnaryDenominator_unary_and_nonempty positiveEndpoints.right
  exact
    And.intro positiveEndpoints.left
      (And.intro positiveEndpoints.right
        (And.intro xData.left
          (And.intro yData.left
            (And.intro xData.right yData.right))))

theorem RealStreamPrefixClassifier_truncated_unary_context_closed
    {x y prefX prefY tailX tailY : Nat -> BHist} :
    (forall i : Nat, UnaryHistory (prefX i)) ->
      (forall i : Nat, hsame (prefX i) (prefY i)) ->
        (forall i : Nat, UnaryHistory (tailX i)) ->
          (forall i : Nat, hsame (tailX i) (tailY i)) ->
            forall {n m : Nat}, RealStreamPrefixClassifier x y (m + n) ->
              RealStreamPrefixClassifier
                (fun i => append (prefX i) (append (x i) (tailX i)))
                (fun i => append (prefY i) (append (y i) (tailY i))) n := by
  intro prefUnary prefSame tailUnary tailSame n m classified
  have truncated : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  exact RealStreamPrefixClassifier_unary_context_closed prefUnary prefSame tailUnary tailSame n
    truncated

theorem RealStreamClassifier_transport_selected_positive_unary_nonempty_package
    {x x' y y' : Nat -> BHist} {n : Nat} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          RatHistoryClassifier (x' n) (y' n) ∧
            PositiveUnaryDenominator (x' n) ∧
              PositiveUnaryDenominator (y' n) ∧
                UnaryHistory (x' n) ∧
                  UnaryHistory (y' n) ∧
                    (hsame (x' n) BHist.Empty -> False) ∧
                      (hsame (y' n) BHist.Empty -> False) := by
  intro sameX sameY classified
  have transported : RatHistoryClassifier (x' n) (y' n) :=
    RatHistoryClassifier_hsame_transport (sameX n) (sameY n) (classified n)
  have positiveRows :
      PositiveUnaryDenominator (x' n) ∧ PositiveUnaryDenominator (y' n) :=
    RatHistoryClassifier_positive_denominators transported
  have leftRows : UnaryHistory (x' n) ∧ (hsame (x' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.left
  have rightRows : UnaryHistory (y' n) ∧ (hsame (y' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.right
  exact And.intro transported
    (And.intro positiveRows.left
      (And.intro positiveRows.right
        (And.intro leftRows.left
          (And.intro rightRows.left (And.intro leftRows.right rightRows.right)))))

theorem RealStreamClassifier_transport_selected_e0_endpoint_absurd
    {x x' y y' : Nat -> BHist} {n : Nat} {zx zy : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          (hsame (x' n) (BHist.e0 zx) -> False) ∧
            (hsame (y' n) (BHist.e0 zy) -> False) := by
  intro sameX sameY classified
  have transported : RatHistoryClassifier (x' n) (y' n) :=
    RatHistoryClassifier_hsame_transport (sameX n) (sameY n) (classified n)
  have positives :
      PositiveUnaryDenominator (x' n) ∧ PositiveUnaryDenominator (y' n) :=
    RatHistoryClassifier_positive_denominators transported
  constructor
  · intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.left)
  · intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.right)

theorem RealStreamClassifier_transported_selected_e1_full_readback_package
    {x x' y y' : Nat -> BHist} {n : Nat} {a b : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) -> RealStreamClassifier x y ->
        hsame (x' n) (BHist.e1 a) -> hsame (y' n) (BHist.e1 b) ->
          RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧
            UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro sameX sameY classified sameLeft sameRight
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RealStreamClassifier_transported_selected_e1_rat_classifier_readback sameX sameY classified
      sameLeft sameRight
  exact And.intro displayed (RatHistoryClassifier_e1_tail_unary_iff.mp displayed)

end BEDC.Derived.RealUp
