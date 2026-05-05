import BEDC.Derived.RealUp.Core
import BEDC.Derived.RealUp.StreamNameTransport

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

def RealUnaryOffsetLe (k w : BHist) : Prop :=
  UnaryHistory k ∧ ∃ tau : BHist, UnaryHistory tau ∧ Cont k tau w

def UnaryOffsetLe (k w : BHist) : Prop :=
  RealUnaryOffsetLe k w

def RealUnaryStreamWindowClassifier (s t : BHist -> BHist) (a w : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory w ∧
    forall k : BHist, UnaryOffsetLe k w ->
      RatHistoryClassifier (s (append a k)) (t (append a k))

theorem RatStreamNameClassifier_real_unary_window_coverage {s t : BHist -> BHist}
    {a w : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> RealUnaryStreamWindowClassifier s t a w := by
  intro _carrierS _carrierT classified aUnary wUnary
  exact ⟨aUnary, wUnary,
    fun k offset => classified.right.right (append a k)
      (unary_append_closed aUnary offset.left)⟩

theorem RealUnaryStreamWindowClassifier_selected_shape_package
    {s t : BHist -> BHist} {a w k u v zS zT : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        hsame (s (append a k)) (BHist.e1 u) ->
          hsame (t (append a k)) (BHist.e1 v) ->
            RatHistoryClassifier (s (append a k)) (t (append a k)) ∧
              RatHistoryClassifier (BHist.e1 u) (BHist.e1 v) ∧ UnaryHistory u ∧
                UnaryHistory v ∧ hsame u v ∧
                  PositiveUnaryDenominator (s (append a k)) ∧
                    PositiveUnaryDenominator (t (append a k)) ∧
                      UnaryHistory (s (append a k)) ∧
                        UnaryHistory (t (append a k)) ∧
                          (hsame (s (append a k)) BHist.Empty -> False) ∧
                            (hsame (t (append a k)) BHist.Empty -> False) ∧
                              (hsame (s (append a k)) (BHist.e0 zS) -> False) ∧
                                (hsame (t (append a k)) (BHist.e0 zT) -> False) := by
  intro carrierS carrierT classified aUnary wUnary offset sameS sameT
  have windowed : RealUnaryStreamWindowClassifier s t a w :=
    RatStreamNameClassifier_real_unary_window_coverage carrierS carrierT classified aUnary wUnary
  have selected : RatHistoryClassifier (s (append a k)) (t (append a k)) :=
    windowed.right.right k offset
  have displayed : RatHistoryClassifier (BHist.e1 u) (BHist.e1 v) :=
    RatHistoryClassifier_hsame_transport sameS sameT selected
  have readback : UnaryHistory u ∧ UnaryHistory v ∧ hsame u v :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  have positives :
      PositiveUnaryDenominator (s (append a k)) ∧
        PositiveUnaryDenominator (t (append a k)) :=
    RatHistoryClassifier_positive_denominators selected
  have leftRows :
      UnaryHistory (s (append a k)) ∧ (hsame (s (append a k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows :
      UnaryHistory (t (append a k)) ∧ (hsame (t (append a k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact ⟨selected, displayed, readback.left, readback.right.left, readback.right.right,
    positives.left, positives.right, leftRows.left, rightRows.left, leftRows.right,
    rightRows.right,
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.left)),
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.right))⟩

theorem RealUnaryStreamWindowClassifier_selected_denominator_package
    {s t : BHist -> BHist} {a w k zS zT : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
      RatHistoryClassifier (s (append a k)) (t (append a k)) ∧
        PositiveUnaryDenominator (s (append a k)) ∧
          PositiveUnaryDenominator (t (append a k)) ∧
            UnaryHistory (s (append a k)) ∧ UnaryHistory (t (append a k)) ∧
              (hsame (s (append a k)) BHist.Empty -> False) ∧
                (hsame (t (append a k)) BHist.Empty -> False) ∧
                  (hsame (s (append a k)) (BHist.e0 zS) -> False) ∧
                    (hsame (t (append a k)) (BHist.e0 zT) -> False) := by
  intro classified aUnary _wUnary offset
  have selected : RatHistoryClassifier (s (append a k)) (t (append a k)) :=
    classified.right.right (append a k) (unary_append_closed aUnary offset.left)
  have positives :
      PositiveUnaryDenominator (s (append a k)) ∧
        PositiveUnaryDenominator (t (append a k)) :=
    RatHistoryClassifier_positive_denominators selected
  have leftRows :
      UnaryHistory (s (append a k)) ∧ (hsame (s (append a k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows :
      UnaryHistory (t (append a k)) ∧ (hsame (t (append a k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact ⟨selected, positives.left, positives.right, leftRows.left, rightRows.left,
    leftRows.right, rightRows.right,
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.left)),
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.right))⟩

theorem RealUnaryStreamWindowClassifier_selected_classifier_appended_tail_package
    {s t : BHist -> BHist} {a w k u v zS zT dS dT : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        hsame (s (append a k)) (BHist.e1 u) ->
          hsame (t (append a k)) (BHist.e1 v) ->
            RatHistoryClassifier (s (append a k)) (t (append a k)) ∧
              RatHistoryClassifier (BHist.e1 u) (BHist.e1 v) ∧ UnaryHistory u ∧
                UnaryHistory v ∧ hsame u v ∧
                  PositiveUnaryDenominator (s (append a k)) ∧
                    PositiveUnaryDenominator (t (append a k)) ∧
                      UnaryHistory (s (append a k)) ∧
                        UnaryHistory (t (append a k)) ∧
                          (hsame (s (append a k)) BHist.Empty -> False) ∧
                            (hsame (t (append a k)) BHist.Empty -> False) ∧
                              (hsame (s (append a k)) (BHist.e0 zS) -> False) ∧
                                (hsame (t (append a k)) (BHist.e0 zT) -> False) ∧
                                  (hsame (s (append a k)) (append dS (BHist.e0 zS)) ->
                                    False) ∧
                                    (hsame (t (append a k)) (append dT (BHist.e0 zT)) ->
                                      False) := by
  intro carrierS carrierT classified aUnary wUnary offset sameS sameT
  have package :=
    RealUnaryStreamWindowClassifier_selected_shape_package
      (s := s) (t := t) (a := a) (w := w) (k := k) (u := u) (v := v)
      (zS := zS) (zT := zT) carrierS carrierT classified aUnary wUnary offset sameS sameT
  exact ⟨package.left, package.right.left, package.right.right.left,
    package.right.right.right.left, package.right.right.right.right.left,
    package.right.right.right.right.right.left, package.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.right.right.right,
    (fun sameAppend =>
      PositiveUnaryDenominator_append_e0_tail_absurd
        (PositiveUnaryDenominator_hsame_transport sameAppend
          package.right.right.right.right.right.left)),
    (fun sameAppend =>
      PositiveUnaryDenominator_append_e0_tail_absurd
        (PositiveUnaryDenominator_hsame_transport sameAppend
          package.right.right.right.right.right.right.left))⟩

def RealStreamWindowClassifier (x y : Nat -> BHist) (n m : Nat) : Prop :=
  forall k : Nat, k <= m -> RatHistoryClassifier (x (n + k)) (y (n + k))

theorem RealStreamWindowClassifier_selected_full_shape_readback_package
    {x y : Nat -> BHist} {n m k : Nat} {a b zX zY : BHist} :
    RealStreamWindowClassifier x y n m -> k <= m -> hsame (x (n + k)) (BHist.e1 a) ->
      hsame (y (n + k)) (BHist.e1 b) ->
        RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧ UnaryHistory a ∧
          UnaryHistory b ∧ hsame a b ∧ PositiveUnaryDenominator (x (n + k)) ∧
            PositiveUnaryDenominator (y (n + k)) ∧ UnaryHistory (x (n + k)) ∧
              UnaryHistory (y (n + k)) ∧ (hsame (x (n + k)) BHist.Empty -> False) ∧
                (hsame (y (n + k)) BHist.Empty -> False) ∧
                  (hsame (x (n + k)) (BHist.e0 zX) -> False) ∧
                    (hsame (y (n + k)) (BHist.e0 zY) -> False) := by
  intro classified windowBound sameX sameY
  have pointClassified : RatHistoryClassifier (x (n + k)) (y (n + k)) :=
    classified k windowBound
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameX sameY pointClassified
  have readback : UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  have positives :
      PositiveUnaryDenominator (x (n + k)) ∧ PositiveUnaryDenominator (y (n + k)) :=
    RatHistoryClassifier_positive_denominators pointClassified
  have leftRows :
      UnaryHistory (x (n + k)) ∧ (hsame (x (n + k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows :
      UnaryHistory (y (n + k)) ∧ (hsame (y (n + k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact ⟨displayed, readback.left, readback.right.left, readback.right.right,
    positives.left, positives.right, leftRows.left, rightRows.left, leftRows.right,
    rightRows.right,
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.left)),
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.right))⟩

theorem RealUnaryStreamWindowClassifier_coverage {s t : BHist -> BHist} {a w : BHist} :
    RealUnaryStreamClassifier s t -> UnaryHistory a -> UnaryHistory w ->
      RealUnaryStreamWindowClassifier s t a w := by
  intro classified aUnary wUnary
  constructor
  · exact aUnary
  · constructor
    · exact wUnary
    · intro k offset
      exact classified (append a k) (unary_append_closed aUnary offset.left)

theorem RealUnaryStreamWindowClassifier_streamName_transported_endpoint_shape_package
    {s t s' t' : BHist -> BHist} {a w k u v zS zT : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        (forall n : BHist, UnaryHistory n -> hsame (s n) (s' n)) ->
          (forall n : BHist, UnaryHistory n -> hsame (t n) (t' n)) ->
            hsame (s' (append a k)) (BHist.e1 u) ->
              hsame (t' (append a k)) (BHist.e1 v) ->
                RatHistoryClassifier (s' (append a k)) (t' (append a k)) ∧
                  PositiveUnaryDenominator (s' (append a k)) ∧
                    PositiveUnaryDenominator (t' (append a k)) ∧
                      UnaryHistory (s' (append a k)) ∧ UnaryHistory (t' (append a k)) ∧
                        (hsame (s' (append a k)) BHist.Empty -> False) ∧
                          (hsame (t' (append a k)) BHist.Empty -> False) ∧
                            (hsame (s' (append a k)) (BHist.e0 zS) -> False) ∧
                              (hsame (t' (append a k)) (BHist.e0 zT) -> False) ∧
                                UnaryHistory u ∧ UnaryHistory v ∧ hsame u v := by
  intro _carrierS _carrierT classified aUnary _wUnary offset sameS sameT sameSE1 sameTE1
  have indexUnary : UnaryHistory (append a k) :=
    unary_append_closed aUnary offset.left
  have transported :
      RatHistoryClassifier (s' (append a k)) (t' (append a k)) :=
    RatHistoryClassifier_hsame_transport (sameS (append a k) indexUnary)
      (sameT (append a k) indexUnary) (classified.right.right (append a k) indexUnary)
  have displayed : RatHistoryClassifier (BHist.e1 u) (BHist.e1 v) :=
    RatHistoryClassifier_hsame_transport sameSE1 sameTE1 transported
  have readback : UnaryHistory u ∧ UnaryHistory v ∧ hsame u v :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  have positives :
      PositiveUnaryDenominator (s' (append a k)) ∧
        PositiveUnaryDenominator (t' (append a k)) :=
    RatHistoryClassifier_positive_denominators transported
  have sRows :
      UnaryHistory (s' (append a k)) ∧
        (hsame (s' (append a k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have tRows :
      UnaryHistory (t' (append a k)) ∧
        (hsame (t' (append a k)) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact ⟨transported, positives.left, positives.right, sRows.left, tRows.left, sRows.right,
    tRows.right,
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.left)),
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.right)),
    readback.left, readback.right.left, readback.right.right⟩

theorem RealUnaryStreamWindowClassifier_restriction_with_offset_witness
    {s t : BHist -> BHist} {a w u : BHist} :
    RealUnaryStreamWindowClassifier s t a u -> UnaryOffsetLe w u ->
      RealUnaryStreamWindowClassifier s t a w ∧
        ∃ tau : BHist, UnaryHistory tau ∧ Cont w tau u := by
  intro window offset
  constructor
  · constructor
    · exact window.left
    · constructor
      · exact offset.left
      · intro k kOffset
        have lifted : UnaryOffsetLe k u := by
          cases kOffset with
          | intro kUnary kTail =>
              cases kTail with
              | intro tau tauData =>
                  cases tauData with
                  | intro tauUnary kTauCont =>
                      cases offset with
                      | intro _wUnary wTail =>
                          cases wTail with
                          | intro sigma sigmaData =>
                              cases sigmaData with
                              | intro sigmaUnary wSigmaCont =>
                                  exact ⟨kUnary, ⟨append tau sigma,
                                    unary_append_closed tauUnary sigmaUnary, by
                                      cases kTauCont
                                      cases wSigmaCont
                                      exact append_assoc k tau sigma⟩⟩
        exact window.right.right k lifted
  · exact offset.right

theorem RealUnaryStreamWindowClassifier_selected_e1_tail_coverage_package
    {s t : BHist -> BHist} {a w k zS zT dS dT : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        exists u : BHist, exists v : BHist,
          hsame (s (append a k)) (BHist.e1 u) ∧
            hsame (t (append a k)) (BHist.e1 v) ∧
              RealUnaryStreamWindowClassifier s t a w ∧
                RatHistoryClassifier (s (append a k)) (t (append a k)) ∧
                  RatHistoryClassifier (BHist.e1 u) (BHist.e1 v) ∧
                    UnaryHistory u ∧ UnaryHistory v ∧ hsame u v ∧
                      PositiveUnaryDenominator (s (append a k)) ∧
                        PositiveUnaryDenominator (t (append a k)) ∧
                          UnaryHistory (s (append a k)) ∧
                            UnaryHistory (t (append a k)) ∧
                              (hsame (s (append a k)) BHist.Empty -> False) ∧
                                (hsame (t (append a k)) BHist.Empty -> False) ∧
                                  (hsame (s (append a k)) (BHist.e0 zS) -> False) ∧
                                    (hsame (t (append a k)) (BHist.e0 zT) -> False) ∧
                                      (hsame (s (append a k))
                                          (append dS (BHist.e0 zS)) -> False) ∧
                                        (hsame (t (append a k))
                                          (append dT (BHist.e0 zT)) -> False) := by
  intro carrierS carrierT classified aUnary wUnary offset
  have windowed : RealUnaryStreamWindowClassifier s t a w :=
    RatStreamNameClassifier_real_unary_window_coverage carrierS carrierT classified aUnary wUnary
  have selected : RatHistoryClassifier (s (append a k)) (t (append a k)) :=
    windowed.right.right k offset
  have positives :
      PositiveUnaryDenominator (s (append a k)) ∧
        PositiveUnaryDenominator (t (append a k)) :=
    RatHistoryClassifier_positive_denominators selected
  cases positives.left with
  | intro u leftPositive =>
      cases positives.right with
      | intro v rightPositive =>
          have sameS : hsame (s (append a k)) (BHist.e1 u) := leftPositive.left
          have sameT : hsame (t (append a k)) (BHist.e1 v) := rightPositive.left
          have displayed : RatHistoryClassifier (BHist.e1 u) (BHist.e1 v) :=
            RatHistoryClassifier_hsame_transport sameS sameT selected
          have readback : UnaryHistory u ∧ UnaryHistory v ∧ hsame u v :=
            RatHistoryClassifier_e1_tail_unary_iff.mp displayed
          have leftRows :
              UnaryHistory (s (append a k)) ∧
                (hsame (s (append a k)) BHist.Empty -> False) :=
            PositiveUnaryDenominator_unary_and_nonempty positives.left
          have rightRows :
              UnaryHistory (t (append a k)) ∧
                (hsame (t (append a k)) BHist.Empty -> False) :=
            PositiveUnaryDenominator_unary_and_nonempty positives.right
          exact ⟨u, v, sameS, sameT, windowed, selected, displayed, readback.left,
            readback.right.left, readback.right.right, positives.left, positives.right,
            leftRows.left, rightRows.left, leftRows.right, rightRows.right,
            (fun sameZero =>
              PositiveUnaryDenominator_e0_absurd
                (PositiveUnaryDenominator_hsame_transport sameZero positives.left)),
            (fun sameZero =>
              PositiveUnaryDenominator_e0_absurd
                (PositiveUnaryDenominator_hsame_transport sameZero positives.right)),
            (fun sameAppendedZero =>
              PositiveUnaryDenominator_append_e0_tail_absurd
                (PositiveUnaryDenominator_hsame_transport sameAppendedZero positives.left)),
            (fun sameAppendedZero =>
              PositiveUnaryDenominator_append_e0_tail_absurd
                (PositiveUnaryDenominator_hsame_transport sameAppendedZero positives.right))⟩

end BEDC.Derived.RealUp
