import BEDC.Derived.IntUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

def PositiveUnaryDenominator (den : BHist) : Prop :=
  ∃ tail : BHist, hsame den (BHist.e1 tail) ∧ UnaryHistory tail

theorem PositiveUnaryDenominator_hsame_transport {d e : BHist} :
    hsame d e -> PositiveUnaryDenominator d -> PositiveUnaryDenominator e := by
  intro same positive
  cases positive with
  | intro tail data =>
      cases data with
      | intro denSame tailUnary =>
          exact ⟨tail, hsame_trans (hsame_symm same) denSame, tailUnary⟩

theorem PositiveUnaryDenominator_append_unary_tail {den tail : BEDC.FKernel.Hist.BHist} :
    PositiveUnaryDenominator den -> BEDC.FKernel.Unary.UnaryHistory tail ->
      PositiveUnaryDenominator (BEDC.FKernel.Cont.append den tail) := by
  intro positive tailUnary
  cases positive with
  | intro denTail data =>
      cases data with
      | intro denSame denTailUnary =>
          have denUnary : BEDC.FKernel.Unary.UnaryHistory den :=
            BEDC.FKernel.Unary.unary_transport
              (BEDC.FKernel.Unary.unary_e1_closed denTailUnary)
              (BEDC.FKernel.Hist.hsame_symm denSame)
          cases BEDC.FKernel.Unary.unary_history_cases tailUnary with
          | inl tailEmpty =>
              cases tailEmpty
              exact ⟨denTail, denSame, denTailUnary⟩
          | inr tailWitness =>
              cases tailWitness with
              | intro tailCore tailData =>
                  cases tailData with
                  | intro tailEq tailCoreUnary =>
                      cases tailEq
                      exact
                        ⟨BEDC.FKernel.Cont.append den tailCore,
                          BEDC.FKernel.Hist.hsame_refl
                            (BEDC.FKernel.Hist.BHist.e1
                              (BEDC.FKernel.Cont.append den tailCore)),
                          BEDC.FKernel.Unary.unary_append_closed denUnary tailCoreUnary⟩

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

theorem RatCarrier_of_int_positive_denominator {sign : BEDC.FKernel.Mark.BMark}
    {numerator denominator : BEDC.FKernel.Hist.BHist} :
    BEDC.Derived.IntUp.IntCarrier sign numerator ->
      PositiveUnaryDenominator denominator -> RatCarrier sign numerator denominator := by
  intro intCarrier positive
  cases positive with
  | intro tail positiveData =>
      cases positiveData with
      | intro sameTail tailUnary =>
          constructor
          · exact intCarrier
          · constructor
            · exact BEDC.FKernel.Unary.unary_transport
                (BEDC.FKernel.Unary.unary_e1_closed tailUnary)
                (BEDC.FKernel.Hist.hsame_symm sameTail)
            · intro sameEmpty
              exact BEDC.FKernel.Hist.not_hsame_e1_empty
                (BEDC.FKernel.Hist.hsame_trans
                  (BEDC.FKernel.Hist.hsame_symm sameTail) sameEmpty)

theorem RatSourceSpec_to_RatCarrier {normalized : BMark -> BHist -> BHist -> Prop}
    {sign : BMark} {num den : BHist} :
    RatSourceSpec normalized sign num den -> RatCarrier sign num den := by
  intro source
  cases source with
  | intro intCarrier sourceRest =>
      cases sourceRest with
      | intro positive _normalized =>
          cases positive with
          | intro tail positiveData =>
              cases positiveData with
              | intro sameDen tailUnary =>
                  constructor
                  · exact intCarrier
                  · constructor
                    · exact unary_transport (unary_e1_closed tailUnary) (hsame_symm sameDen)
                    · intro sameEmpty
                      exact not_hsame_e1_empty (hsame_trans (hsame_symm sameDen) sameEmpty)

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

theorem RatCarrier_iff_positive_unary_denominator {sign : BEDC.FKernel.Mark.BMark}
    {num den : BEDC.FKernel.Hist.BHist} :
    RatCarrier sign num den ↔
      BEDC.Derived.IntUp.IntCarrier sign num ∧ PositiveUnaryDenominator den := by
  constructor
  · intro carrier
    cases carrier with
    | intro intCarrier rest =>
        cases rest with
        | intro denUnary denNonempty =>
            constructor
            · exact intCarrier
            · cases unary_history_empty_or_e1_tail denUnary with
              | inl denEmpty =>
                  cases denEmpty
                  exact False.elim (denNonempty (hsame_refl BHist.Empty))
              | inr denTail =>
                  cases denTail with
                  | intro tail tailData =>
                      cases tailData with
                      | intro denEq tailUnary =>
                          cases denEq
                          exact ⟨tail, hsame_refl (BHist.e1 tail), tailUnary⟩
  · intro data
    cases data with
    | intro intCarrier positive =>
        cases positive with
        | intro tail positiveData =>
            cases positiveData with
            | intro denSame tailUnary =>
                constructor
                · exact intCarrier
                · constructor
                  · exact unary_transport (unary_e1_closed tailUnary) (hsame_symm denSame)
                  · intro denEmpty
                    exact not_hsame_e1_empty (hsame_trans (hsame_symm denSame) denEmpty)

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
