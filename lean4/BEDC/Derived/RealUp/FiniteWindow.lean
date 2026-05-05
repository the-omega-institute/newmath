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

theorem UnaryOffsetLe_cont_trans {k w u tau sigma : BHist} :
    UnaryHistory k -> UnaryHistory tau -> UnaryHistory sigma -> Cont k tau w ->
      Cont w sigma u -> UnaryOffsetLe k u := by
  intro kUnary tauUnary sigmaUnary leftCont rightCont
  exact ⟨kUnary, ⟨append tau sigma, unary_append_closed tauUnary sigmaUnary, by
    cases leftCont
    cases rightCont
    exact append_assoc k tau sigma⟩⟩

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

theorem RealUnaryStreamWindowClassifier_selected_canonical_e1_tail_witness
    {s t : BHist -> BHist} {a w k : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        exists u : BHist, exists v : BHist,
          hsame (s (append a k)) (BHist.e1 u) ∧
            hsame (t (append a k)) (BHist.e1 v) ∧
              UnaryHistory u ∧ UnaryHistory v ∧ hsame u v ∧
                (forall u' v' : BHist,
                  hsame (s (append a k)) (BHist.e1 u') ∧
                    hsame (t (append a k)) (BHist.e1 v') ->
                      UnaryHistory u' ∧ UnaryHistory v' ∧ hsame u u' ∧
                        hsame v v' ∧ hsame u' v ∧ hsame u v') := by
  intro carrierS carrierT classified aUnary wUnary offset
  have package :=
    RealUnaryStreamWindowClassifier_selected_e1_tail_coverage_package
      (s := s) (t := t) (a := a) (w := w) (k := k)
      (zS := BHist.Empty) (zT := BHist.Empty) (dS := BHist.Empty) (dT := BHist.Empty)
      carrierS carrierT classified aUnary wUnary offset
  cases package with
  | intro u packageU =>
      cases packageU with
      | intro v data =>
          exact ⟨u, v, data.left, data.right.left, data.right.right.right.right.right.left,
            data.right.right.right.right.right.right.left,
            data.right.right.right.right.right.right.right.left, fun u' v' displayed =>
              have displayedClassifier : RatHistoryClassifier (BHist.e1 u') (BHist.e1 v') :=
                RatHistoryClassifier_hsame_transport displayed.left displayed.right
                  data.right.right.right.left
              have displayedReadback : UnaryHistory u' ∧ UnaryHistory v' ∧ hsame u' v' :=
                RatHistoryClassifier_e1_tail_unary_iff.mp displayedClassifier
              have sameUU' : hsame u u' :=
                hsame_e1_iff.mp (hsame_trans (hsame_symm data.left) displayed.left)
              have sameVV' : hsame v v' :=
                hsame_e1_iff.mp
                  (hsame_trans (hsame_symm data.right.left) displayed.right)
              ⟨displayedReadback.left, displayedReadback.right.left, sameUU', sameVV',
                hsame_trans (hsame_symm sameUU')
                  data.right.right.right.right.right.right.right.left,
                hsame_trans data.right.right.right.right.right.right.right.left sameVV'⟩⟩

theorem RealUnaryStreamWindowClassifier_selected_e1_tail_pairwise_coherence
    {s t : BHist -> BHist} {a w k u uPrime v vPrime : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        hsame (s (append a k)) (BHist.e1 u) ->
          hsame (s (append a k)) (BHist.e1 uPrime) ->
            hsame (t (append a k)) (BHist.e1 v) ->
              hsame (t (append a k)) (BHist.e1 vPrime) ->
                UnaryHistory u ∧ UnaryHistory uPrime ∧ UnaryHistory v ∧
                  UnaryHistory vPrime ∧ hsame u uPrime ∧ hsame v vPrime ∧
                    hsame u v ∧ hsame uPrime vPrime ∧ hsame u vPrime ∧
                      hsame uPrime v := by
  intro carrierS carrierT classified aUnary wUnary offset sameSU sameSUPrime sameTV
    sameTVPrime
  have first :=
    RealUnaryStreamWindowClassifier_selected_shape_package
      (s := s) (t := t) (a := a) (w := w) (k := k) (u := u) (v := v)
      (zS := u) (zT := v)
      carrierS carrierT classified aUnary wUnary offset sameSU sameTV
  have second :=
    RealUnaryStreamWindowClassifier_selected_shape_package
      (s := s) (t := t) (a := a) (w := w) (k := k) (u := uPrime) (v := vPrime)
      (zS := uPrime) (zT := vPrime)
      carrierS carrierT classified aUnary wUnary offset sameSUPrime sameTVPrime
  have sameUUPrime : hsame u uPrime :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameSU) sameSUPrime)
  have sameVVPrime : hsame v vPrime :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameTV) sameTVPrime)
  have sameUV : hsame u v :=
    first.right.right.right.right.left
  have sameUPrimeVPrime : hsame uPrime vPrime :=
    second.right.right.right.right.left
  have sameUVPrime : hsame u vPrime :=
    hsame_trans sameUV sameVVPrime
  have sameUPrimeV : hsame uPrime v :=
    hsame_trans (hsame_symm sameUUPrime) sameUV
  exact ⟨first.right.right.left, second.right.right.left, first.right.right.right.left,
    second.right.right.right.left, sameUUPrime, sameVVPrime, sameUV, sameUPrimeVPrime,
    sameUVPrime, sameUPrimeV⟩

theorem RealUnaryStreamWindowClassifier_selected_tail_class_exactness
    {s t : BHist -> BHist} {a w k : BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t -> RatStreamNameClassifier s t ->
      UnaryHistory a -> UnaryHistory w -> UnaryOffsetLe k w ->
        exists u : BHist, exists v : BHist,
          hsame (s (append a k)) (BHist.e1 u) ∧
            hsame (t (append a k)) (BHist.e1 v) ∧
              UnaryHistory u ∧ UnaryHistory v ∧ hsame u v ∧
                (forall u' v' : BHist,
                  (hsame (s (append a k)) (BHist.e1 u') ∧
                    hsame (t (append a k)) (BHist.e1 v')) ↔
                      (UnaryHistory u' ∧ UnaryHistory v' ∧ hsame u u' ∧ hsame v v')) := by
  intro carrierS carrierT classified aUnary wUnary offset
  have witness :=
    RealUnaryStreamWindowClassifier_selected_canonical_e1_tail_witness
      (s := s) (t := t) (a := a) (w := w) (k := k)
      carrierS carrierT classified aUnary wUnary offset
  cases witness with
  | intro u witnessU =>
      cases witnessU with
      | intro v data =>
          exact ⟨u, v, data.left, data.right.left, data.right.right.left,
            data.right.right.right.left, data.right.right.right.right.left,
            fun u' v' =>
              Iff.intro
                (fun displayed =>
                  have coherence := data.right.right.right.right.right u' v' displayed
                  ⟨coherence.left, coherence.right.left, coherence.right.right.left,
                    coherence.right.right.right.left⟩)
                (fun selected =>
                  ⟨hsame_trans data.left (hsame_e1_congr selected.right.right.left),
                    hsame_trans data.right.left
                      (hsame_e1_congr selected.right.right.right)⟩)⟩

end BEDC.Derived.RealUp
