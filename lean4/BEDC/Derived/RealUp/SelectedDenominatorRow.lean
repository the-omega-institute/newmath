import BEDC.Derived.RealUp.FiniteWindow

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

def RealUnarySelectedDenominatorRow (s t : BHist -> BHist) (n : BHist) : Prop :=
  RatHistoryClassifier (s n) (t n) ∧ PositiveUnaryDenominator (s n) ∧
    PositiveUnaryDenominator (t n) ∧ UnaryHistory (s n) ∧ UnaryHistory (t n) ∧
      (hsame (s n) BHist.Empty -> False) ∧ (hsame (t n) BHist.Empty -> False) ∧
        forall z : BHist,
          (hsame (s n) (BHist.e0 z) -> False) ∧
            (hsame (t n) (BHist.e0 z) -> False)

theorem RealUnarySelectedDenominatorRow_streamName_equivalence {s t : BHist -> BHist} :
    RatStreamNameCarrier s -> RatStreamNameCarrier t ->
      (RatStreamNameClassifier s t ->
        RealUnaryStreamClassifier s t ∧
          forall n : BHist, UnaryHistory n -> RealUnarySelectedDenominatorRow s t n) ∧
      (RealUnaryStreamClassifier s t ->
        RatStreamNameClassifier s t ∧
          forall n : BHist, UnaryHistory n -> RealUnarySelectedDenominatorRow s t n) ∧
      ((forall n : BHist, UnaryHistory n -> RealUnarySelectedDenominatorRow s t n) ->
        RatStreamNameClassifier s t ∧ RealUnaryStreamClassifier s t) := by
  intro carrierS carrierT
  have rowFromRat :
      RatStreamNameClassifier s t ->
        forall n : BHist, UnaryHistory n -> RealUnarySelectedDenominatorRow s t n := by
    intro classified n nUnary
    have point : RatHistoryClassifier (s n) (t n) :=
      classified.right.right n nUnary
    have positives :
        PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) :=
      RatHistoryClassifier_positive_denominators point
    have leftRows :
        UnaryHistory (s n) ∧ (hsame (s n) BHist.Empty -> False) :=
      PositiveUnaryDenominator_unary_and_nonempty positives.left
    have rightRows :
        UnaryHistory (t n) ∧ (hsame (t n) BHist.Empty -> False) :=
      PositiveUnaryDenominator_unary_and_nonempty positives.right
    exact And.intro point
      (And.intro positives.left
        (And.intro positives.right
          (And.intro leftRows.left
            (And.intro rightRows.left
              (And.intro leftRows.right
                (And.intro rightRows.right
                  (fun _z =>
                    And.intro
                      (fun sameZero =>
                        PositiveUnaryDenominator_e0_absurd
                          (PositiveUnaryDenominator_hsame_transport sameZero positives.left))
                      (fun sameZero =>
                        PositiveUnaryDenominator_e0_absurd
                          (PositiveUnaryDenominator_hsame_transport sameZero
                            positives.right)))))))))
  have ratFromRows :
      (forall n : BHist, UnaryHistory n -> RealUnarySelectedDenominatorRow s t n) ->
        RatStreamNameClassifier s t := by
    intro rows
    exact And.intro carrierS
      (And.intro carrierT (fun n nUnary => (rows n nUnary).left))
  constructor
  · intro classified
    exact And.intro classified.right.right (rowFromRat classified)
  · constructor
    · intro classified
      have stream : RatStreamNameClassifier s t :=
        And.intro carrierS (And.intro carrierT classified)
      exact And.intro stream (rowFromRat stream)
    · intro rows
      have stream : RatStreamNameClassifier s t := ratFromRows rows
      exact And.intro stream stream.right.right

end BEDC.Derived.RealUp
