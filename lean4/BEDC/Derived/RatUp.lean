import BEDC.Derived.IntUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

def PositiveUnaryDenominator (den : BHist) : Prop :=
  ∃ tail : BHist, hsame den (BHist.e1 tail) ∧ UnaryHistory tail

def rat_classifier_spec_trans_positive_unary_denominator_carrier
    (sign : BEDC.FKernel.Mark.BMark)
    (numerator denominator : BEDC.FKernel.Hist.BHist) : Prop :=
  BEDC.Derived.IntUp.IntCarrier sign numerator ∧
    BEDC.FKernel.Unary.UnaryHistory denominator ∧
      ∃ tail : BEDC.FKernel.Hist.BHist,
        denominator = BEDC.FKernel.Hist.BHist.e1 tail ∧
          BEDC.FKernel.Unary.UnaryHistory tail

def RatSourceSpec (normalized : BMark → BHist → BHist → Prop) (sign : BMark)
    (num den : BHist) : Prop :=
  BEDC.Derived.IntUp.IntCarrier sign num ∧ PositiveUnaryDenominator den ∧
    normalized sign num den

def RatCarrier
    (sign : BEDC.FKernel.Mark.BMark) (numerator denominator : BEDC.FKernel.Hist.BHist) :
    Prop :=
  BEDC.Derived.IntUp.IntCarrier sign numerator ∧
    BEDC.FKernel.Unary.UnaryHistory denominator ∧
      (BEDC.FKernel.Hist.hsame denominator BEDC.FKernel.Hist.BHist.Empty → False)

theorem RatCarrier_positive_denominator {sign : BEDC.FKernel.Mark.BMark}
    {numerator denominator : BEDC.FKernel.Hist.BHist} :
    RatCarrier sign numerator denominator -> PositiveUnaryDenominator denominator := by
  intro carrier
  cases carrier with
  | intro _ denominatorData =>
      cases denominatorData with
      | intro denominatorUnary denominatorNonempty =>
          cases unary_history_cases denominatorUnary with
          | inl denominatorEmpty =>
              cases denominatorEmpty
              exact False.elim (denominatorNonempty (hsame_refl BHist.Empty))
          | inr tailWitness =>
              cases tailWitness with
              | intro tail tailData =>
                  cases tailData with
                  | intro denominatorEq tailUnary =>
                      cases denominatorEq
                      exact ⟨tail, hsame_refl (BHist.e1 tail), tailUnary⟩

def rat_classifier_spec_trans_carrier
    (sign : BEDC.FKernel.Mark.BMark) (numerator denominator : BEDC.FKernel.Hist.BHist) :
    Prop :=
  RatCarrier sign numerator denominator

def RatClassifierSpec
    (s1 : BEDC.FKernel.Mark.BMark) (n1 d1 : BEDC.FKernel.Hist.BHist)
    (s2 : BEDC.FKernel.Mark.BMark) (n2 d2 : BEDC.FKernel.Hist.BHist) : Prop :=
  rat_classifier_spec_trans_carrier s1 n1 d1 ∧
    rat_classifier_spec_trans_carrier s2 n2 d2 ∧
      BEDC.FKernel.Mark.msame s1 s2 ∧
        BEDC.FKernel.Hist.hsame n1 n2 ∧
          BEDC.FKernel.Hist.hsame d1 d2

theorem RatClassifierSpec_trans
    {s1 s2 s3 : BEDC.FKernel.Mark.BMark}
    {n1 n2 n3 d1 d2 d3 : BEDC.FKernel.Hist.BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 →
      RatClassifierSpec s2 n2 d2 s3 n3 d3 →
        RatClassifierSpec s1 n1 d1 s3 n3 d3 := by
  intro left right
  cases left with
  | intro carrier1 leftRest =>
      cases leftRest with
      | intro _ leftRest =>
          cases leftRest with
          | intro sign12 leftRest =>
              cases leftRest with
              | intro numerator12 denominator12 =>
                  cases right with
                  | intro _ rightRest =>
                      cases rightRest with
                      | intro carrier3 rightRest =>
                          cases rightRest with
                          | intro sign23 rightRest =>
                              cases rightRest with
                              | intro numerator23 denominator23 =>
                                  constructor
                                  · exact carrier1
                                  · constructor
                                    · exact carrier3
                                    · constructor
                                      · exact BEDC.FKernel.Mark.msame_trans sign12 sign23
                                      · constructor
                                        · exact BEDC.FKernel.Hist.hsame_trans numerator12 numerator23
                                        · exact BEDC.FKernel.Hist.hsame_trans denominator12 denominator23

end BEDC.Derived.RatUp
