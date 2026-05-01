import BEDC.Derived.IntUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def PositiveUnaryDenominator (den : BHist) : Prop :=
  ∃ tail : BHist, hsame den (BHist.e1 tail) ∧ UnaryHistory tail

theorem PositiveUnaryDenominator_e1_iff_unary {tail : BHist} :
    PositiveUnaryDenominator (BHist.e1 tail) ↔ UnaryHistory tail := by
  constructor
  · intro positive
    cases positive with
    | intro witness data =>
        cases data with
        | intro same witnessUnary =>
            exact unary_transport witnessUnary (hsame_symm (hsame_e1_iff.mp same))
  · intro tailUnary
    exact ⟨tail, hsame_refl (BHist.e1 tail), tailUnary⟩

theorem PositiveUnaryDenominator_not_empty {den : BHist} :
    PositiveUnaryDenominator den -> hsame den BHist.Empty -> False := by
  intro positive sameEmpty
  cases positive with
  | intro tail data =>
      cases data with
      | intro sameTail _tailUnary =>
          exact not_hsame_e1_empty (hsame_trans (hsame_symm sameTail) sameEmpty)

theorem PositiveUnaryDenominator_hsame_transport {d e : BHist} :
    hsame d e -> PositiveUnaryDenominator d -> PositiveUnaryDenominator e := by
  intro same positive
  cases positive with
  | intro tail data =>
      cases data with
      | intro denSame tailUnary =>
          exact ⟨tail, hsame_trans (hsame_symm same) denSame, tailUnary⟩

theorem PositiveUnaryDenominator_unary_and_nonempty {den : BHist} :
    PositiveUnaryDenominator den -> UnaryHistory den /\ (hsame den BHist.Empty -> False) := by
  intro positive
  cases positive with
  | intro tail data =>
      cases data with
      | intro sameTail tailUnary =>
          constructor
          · exact unary_transport (unary_e1_closed tailUnary) (hsame_symm sameTail)
          · intro sameEmpty
            exact not_hsame_e1_empty (hsame_trans (hsame_symm sameTail) sameEmpty)

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

theorem PositiveUnaryDenominator_append_unary_prefix {«prefix» den : BHist} :
    UnaryHistory «prefix» → PositiveUnaryDenominator den →
      PositiveUnaryDenominator (BEDC.FKernel.Cont.append «prefix» den) := by
  intro prefixUnary positive
  cases positive with
  | intro tail data =>
      cases data with
      | intro denSame tailUnary =>
          cases denSame
          exact ⟨BEDC.FKernel.Cont.append «prefix» tail,
            hsame_refl (BHist.e1 (BEDC.FKernel.Cont.append «prefix» tail)),
            unary_append_closed prefixUnary tailUnary⟩

theorem PositiveUnaryDenominator_e0_absurd {tail : BHist} :
    PositiveUnaryDenominator (BHist.e0 tail) -> False := by
  intro positive
  cases positive with
  | intro witness data =>
      exact not_hsame_e0_e1 data.left

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

theorem RatCarrier_denominator_hsame_transport {sign : BEDC.FKernel.Mark.BMark}
    {numerator denominator denominator2 : BHist} :
    RatCarrier sign numerator denominator -> hsame denominator denominator2 ->
      RatCarrier sign numerator denominator2 := by
  intro carrier sameDenominator
  cases carrier with
  | intro intCarrier denominatorData =>
      exact RatCarrier_of_int_positive_denominator intCarrier
        (PositiveUnaryDenominator_hsame_transport sameDenominator
          (RatCarrier_positive_denominator ⟨intCarrier, denominatorData⟩))

def RatHistoryCarrier (denominator : BHist) : Prop :=
  ∃ sign : BMark, ∃ numerator : BHist, RatCarrier sign numerator denominator

theorem RatHistoryCarrier_iff_positive_denominator {d : BHist} :
    RatHistoryCarrier d <-> PositiveUnaryDenominator d := by
  constructor
  · intro carrier
    cases carrier with
    | intro _ signData =>
        cases signData with
        | intro _ ratCarrier =>
            exact RatCarrier_positive_denominator ratCarrier
  · intro positive
    have intCarrier : BEDC.Derived.IntUp.IntCarrier BMark.b0 BHist.Empty := by
      constructor
      · exact Or.inl rfl
      · exact unary_empty
    exact ⟨BMark.b0, BHist.Empty, RatCarrier_of_int_positive_denominator intCarrier positive⟩

theorem RatHistoryCarrier_not_empty {d : BHist} :
    RatHistoryCarrier d -> hsame d BHist.Empty -> False := by
  intro carrier sameEmpty
  cases carrier with
  | intro sign signData =>
      cases signData with
      | intro numerator ratCarrier =>
          exact PositiveUnaryDenominator_not_empty
            (RatCarrier_positive_denominator ratCarrier) sameEmpty

def RatHistoryClassifier (d e : BHist) : Prop :=
  RatHistoryCarrier d ∧ RatHistoryCarrier e ∧ hsame d e

def RatHistoryLedgerPolicy (raw visible : BHist) : Prop :=
  RatHistoryCarrier raw ∧ hsame raw visible

theorem RatHistoryClassifier_trans {d e f : BHist} :
    RatHistoryClassifier d e -> RatHistoryClassifier e f -> RatHistoryClassifier d f := by
  intro de ef
  cases de with
  | intro carrierD deRest =>
      cases deRest with
      | intro _carrierE sameDE =>
          cases ef with
          | intro _carrierE' efRest =>
              cases efRest with
              | intro carrierF sameEF =>
                  exact ⟨carrierD, carrierF, hsame_trans sameDE sameEF⟩

theorem RatHistoryClassifier_symm {d e : BEDC.FKernel.Hist.BHist} :
    RatHistoryClassifier d e -> RatHistoryClassifier e d := by
  intro classifier
  cases classifier with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE sameDE =>
          exact ⟨carrierE, carrierD, hsame_symm sameDE⟩

theorem RatHistoryCarrier_hsame_transport {d e : BHist} :
    hsame d e -> RatHistoryCarrier d -> RatHistoryCarrier e := by
  intro same carrier
  cases carrier with
  | intro sign signData =>
      cases signData with
      | intro numerator ratCarrier =>
          exact ⟨sign, numerator, RatCarrier_denominator_hsame_transport ratCarrier same⟩

theorem RatHistoryClassifier_hsame_transport {d d' e e' : BHist} :
    hsame d d' -> hsame e e' ->
      RatHistoryClassifier d e -> RatHistoryClassifier d' e' := by
  intro sameD sameE classified
  cases classified with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE sameDE =>
          exact ⟨RatHistoryCarrier_hsame_transport sameD carrierD,
            RatHistoryCarrier_hsame_transport sameE carrierE,
              hsame_trans (hsame_symm sameD) (hsame_trans sameDE sameE)⟩

theorem RatHistoryLedgerPolicy_visible_carrier {raw visible : BHist} :
    RatHistoryLedgerPolicy raw visible → RatHistoryCarrier visible := by
  intro ledger
  exact RatHistoryCarrier_hsame_transport ledger.right ledger.left

theorem RatHistoryLedgerPolicy_hsame_transport {raw raw' visible visible' : BHist} :
    RatHistoryLedgerPolicy raw visible -> hsame raw raw' -> hsame visible visible' ->
      RatHistoryLedgerPolicy raw' visible' := by
  intro ledger sameRaw sameVisible
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      constructor
      · exact RatHistoryCarrier_hsame_transport sameRaw rawCarrier
      · exact hsame_trans (hsame_trans (hsame_symm sameRaw) sameRawVisible) sameVisible

theorem RatHistoryLedgerPolicy_raw_visible_classifier {raw visible : BHist} :
    RatHistoryLedgerPolicy raw visible -> RatHistoryClassifier raw visible := by
  intro ledger
  exact ⟨ledger.left, RatHistoryLedgerPolicy_visible_carrier ledger, ledger.right⟩

theorem rat_history_semantic_name_certificate :
    SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier
      RatHistoryClassifier := by
  constructor
  · constructor
    · exact ⟨BHist.e1 BHist.Empty, BMark.b0, BHist.Empty,
        ⟨Or.inl rfl, unary_empty⟩, unary_e1_closed unary_empty,
          fun sameEmpty => not_hsame_e1_empty sameEmpty⟩
    · intro h carrier
      exact ⟨carrier, carrier, hsame_refl h⟩
    · intro h k same
      exact ⟨same.right.left, same.left, hsame_symm same.right.right⟩
    · intro h k r hk kr
      exact ⟨hk.left, RatHistoryCarrier_hsame_transport
        (hsame_trans hk.right.right kr.right.right) hk.left,
          hsame_trans hk.right.right kr.right.right⟩
    · intro h k same carrier
      exact RatHistoryCarrier_hsame_transport same.right.right carrier
  · intro h source
    exact source
  · intro h source
    exact source

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
                      exact not_hsame_e1_empty
                        (hsame_trans (hsame_symm sameDen) sameEmpty)

theorem RatCarrier_hsame_transport {s t : BMark} {n n' d d' : BHist} :
    RatCarrier s n d -> msame s t -> hsame n n' -> hsame d d' -> RatCarrier t n' d' := by
  intro carrier sameSign sameNumerator sameDenominator
  cases sameSign
  cases carrier with
  | intro intCarrier denominatorData =>
      cases denominatorData with
      | intro denominatorUnary denominatorNonempty =>
          constructor
          · exact IntUp.IntCarrier_magnitude_hsame_transport intCarrier sameNumerator
          · constructor
            · exact unary_transport denominatorUnary sameDenominator
            · intro sameEmpty
              exact denominatorNonempty (hsame_trans sameDenominator sameEmpty)

def RatClassifierSpec
    (s1 : BEDC.FKernel.Mark.BMark) (n1 d1 : BEDC.FKernel.Hist.BHist)
    (s2 : BEDC.FKernel.Mark.BMark) (n2 d2 : BEDC.FKernel.Hist.BHist) : Prop :=
  RatCarrier s1 n1 d1 ∧
    RatCarrier s2 n2 d2 ∧
      BEDC.FKernel.Mark.msame s1 s2 ∧
        BEDC.FKernel.Hist.hsame n1 n2 ∧
          BEDC.FKernel.Hist.hsame d1 d2

theorem RatClassifierSpec_refl {s : BEDC.FKernel.Mark.BMark}
    {n d : BEDC.FKernel.Hist.BHist} :
    RatCarrier s n d -> RatClassifierSpec s n d s n d := by
  intro carrier
  constructor
  · exact carrier
  · constructor
    · exact carrier
    · constructor
      · exact BEDC.FKernel.Mark.msame_refl s
      · constructor
        · exact BEDC.FKernel.Hist.hsame_refl n
        · exact BEDC.FKernel.Hist.hsame_refl d

theorem RatClassifierSpec_positive_denominators {s1 s2 : BEDC.FKernel.Mark.BMark}
    {n1 n2 d1 d2 : BEDC.FKernel.Hist.BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 ->
      PositiveUnaryDenominator d1 /\ PositiveUnaryDenominator d2 := by
  intro classifier
  cases classifier with
  | intro carrier1 rest =>
      cases rest with
      | intro carrier2 _ =>
          constructor
          · exact RatCarrier_positive_denominator carrier1
          · exact RatCarrier_positive_denominator carrier2

theorem RatClassifierSpec_denominator_positive_transport {s1 s2 : BMark}
    {n1 n2 d1 d2 d1' d2' : BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 -> hsame d1 d1' -> hsame d2 d2' ->
      PositiveUnaryDenominator d1' /\ PositiveUnaryDenominator d2' := by
  intro classifier sameD1 sameD2
  cases classifier with
  | intro carrier1 rest =>
      cases rest with
      | intro carrier2 _ =>
          constructor
          · exact PositiveUnaryDenominator_hsame_transport sameD1
              (RatCarrier_positive_denominator carrier1)
          · exact PositiveUnaryDenominator_hsame_transport sameD2
              (RatCarrier_positive_denominator carrier2)

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

theorem RatCarrier_append_unary_denominator_closed {sign : BEDC.FKernel.Mark.BMark}
    {numerator denominator tail : BEDC.FKernel.Hist.BHist} :
    RatCarrier sign numerator denominator -> BEDC.FKernel.Unary.UnaryHistory tail ->
      RatCarrier sign numerator (BEDC.FKernel.Cont.append denominator tail) := by
  intro carrier tailUnary
  cases Iff.mp RatCarrier_iff_positive_unary_denominator carrier with
  | intro intCarrier positiveDenominator =>
      exact RatCarrier_of_int_positive_denominator intCarrier
        (PositiveUnaryDenominator_append_unary_tail positiveDenominator tailUnary)

theorem RatHistoryCarrier_append_unary_denominator_closed {d tail : BHist} :
    RatHistoryCarrier d -> UnaryHistory tail ->
      RatHistoryCarrier (BEDC.FKernel.Cont.append d tail) := by
  intro carrier tailUnary
  cases carrier with
  | intro sign signData =>
      cases signData with
      | intro numerator ratCarrier =>
          exact
            ⟨sign, numerator, RatCarrier_append_unary_denominator_closed ratCarrier tailUnary⟩

theorem RatCarrier_prepend_unary_denominator_closed {sign : BMark}
    {numerator denominator pref : BHist} :
    UnaryHistory pref -> RatCarrier sign numerator denominator ->
      RatCarrier sign numerator (BEDC.FKernel.Cont.append pref denominator) := by
  intro prefUnary carrier
  cases Iff.mp RatCarrier_iff_positive_unary_denominator carrier with
  | intro intCarrier positiveDenominator =>
      exact RatCarrier_of_int_positive_denominator intCarrier
        (PositiveUnaryDenominator_append_unary_prefix prefUnary positiveDenominator)

theorem RatHistoryCarrier_prepend_unary_denominator_closed {d pref : BHist} :
    UnaryHistory pref -> RatHistoryCarrier d ->
      RatHistoryCarrier (BEDC.FKernel.Cont.append pref d) := by
  intro prefUnary carrier
  cases carrier with
  | intro sign signData =>
      cases signData with
      | intro numerator ratCarrier =>
          exact
            ⟨sign, numerator,
              RatCarrier_prepend_unary_denominator_closed prefUnary ratCarrier⟩

theorem RatClassifierSpec_append_unary_denominators_closed {s1 s2 : BMark}
    {n1 n2 d1 d2 tail1 tail2 : BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 -> UnaryHistory tail1 -> hsame tail1 tail2 ->
      RatClassifierSpec s1 n1 (BEDC.FKernel.Cont.append d1 tail1)
        s2 n2 (BEDC.FKernel.Cont.append d2 tail2) := by
  intro classifier tail1Unary sameTail
  cases classifier with
  | intro carrier1 rest =>
      cases rest with
      | intro carrier2 rest =>
          cases rest with
          | intro sameSign rest =>
              cases rest with
              | intro sameNumerator sameDenominator =>
                  have tail2Unary : UnaryHistory tail2 := unary_transport tail1Unary sameTail
                  have carrier1App :
                      RatCarrier s1 n1 (BEDC.FKernel.Cont.append d1 tail1) :=
                    RatCarrier_append_unary_denominator_closed carrier1 tail1Unary
                  have carrier2App :
                      RatCarrier s2 n2 (BEDC.FKernel.Cont.append d2 tail2) :=
                    RatCarrier_append_unary_denominator_closed carrier2 tail2Unary
                  have denominatorAppSame :
                      hsame (BEDC.FKernel.Cont.append d1 tail1)
                        (BEDC.FKernel.Cont.append d2 tail2) := by
                    cases sameDenominator
                    cases sameTail
                    exact hsame_refl (BEDC.FKernel.Cont.append d1 tail1)
                  exact ⟨carrier1App, carrier2App, sameSign, sameNumerator, denominatorAppSame⟩

theorem RatClassifierSpec_prepend_unary_denominators_closed {s1 s2 : BMark}
    {n1 n2 d1 d2 pref1 pref2 : BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 -> UnaryHistory pref1 -> hsame pref1 pref2 ->
      RatClassifierSpec s1 n1 (BEDC.FKernel.Cont.append pref1 d1)
        s2 n2 (BEDC.FKernel.Cont.append pref2 d2) := by
  intro classifier pref1Unary samePref
  cases classifier with
  | intro carrier1 rest =>
      cases rest with
      | intro carrier2 rest =>
          cases rest with
          | intro sameSign rest =>
              cases rest with
              | intro sameNumerator sameDenominator =>
                  have pref2Unary : UnaryHistory pref2 := unary_transport pref1Unary samePref
                  have carrier1Pre :
                      RatCarrier s1 n1 (BEDC.FKernel.Cont.append pref1 d1) :=
                    RatCarrier_prepend_unary_denominator_closed pref1Unary carrier1
                  have carrier2Pre :
                      RatCarrier s2 n2 (BEDC.FKernel.Cont.append pref2 d2) :=
                    RatCarrier_prepend_unary_denominator_closed pref2Unary carrier2
                  have denominatorPreSame :
                      hsame (BEDC.FKernel.Cont.append pref1 d1)
                        (BEDC.FKernel.Cont.append pref2 d2) := by
                    cases samePref
                    cases sameDenominator
                    exact hsame_refl (BEDC.FKernel.Cont.append pref1 d1)
                  exact
                    ⟨carrier1Pre, carrier2Pre, sameSign, sameNumerator, denominatorPreSame⟩

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

theorem RatClassifierSpec_symm
    {s1 s2 : BEDC.FKernel.Mark.BMark} {n1 n2 d1 d2 : BEDC.FKernel.Hist.BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 ->
      RatClassifierSpec s2 n2 d2 s1 n1 d1 := by
  intro classifier
  cases classifier with
  | intro carrier1 rest =>
      cases rest with
      | intro carrier2 rest =>
          cases rest with
          | intro sameSign rest =>
              cases rest with
              | intro sameNumerator sameDenominator =>
                  constructor
                  · exact carrier2
                  · constructor
                    · exact carrier1
                    · constructor
                      · exact BEDC.FKernel.Mark.msame_symm sameSign
                      · constructor
                        · exact BEDC.FKernel.Hist.hsame_symm sameNumerator
                        · exact BEDC.FKernel.Hist.hsame_symm sameDenominator

theorem RatClassifierSpec_component_transport {s1 s2 t1 t2 : BMark}
    {n1 n2 n1' n2' d1 d2 d1' d2' : BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 -> msame s1 t1 -> msame s2 t2 ->
      hsame n1 n1' -> hsame n2 n2' -> hsame d1 d1' -> hsame d2 d2' ->
        RatClassifierSpec t1 n1' d1' t2 n2' d2' := by
  intro classifier sameS1 sameS2 sameN1 sameN2 sameD1 sameD2
  cases classifier with
  | intro carrier1 rest =>
      cases rest with
      | intro carrier2 rest =>
          cases rest with
          | intro sameSign rest =>
              cases rest with
              | intro sameNumerator sameDenominator =>
                  constructor
                  · exact RatCarrier_hsame_transport carrier1 sameS1 sameN1 sameD1
                  · constructor
                    · exact RatCarrier_hsame_transport carrier2 sameS2 sameN2 sameD2
                    · constructor
                      · exact msame_trans (msame_trans (msame_symm sameS1) sameSign) sameS2
                      · constructor
                        · exact hsame_trans (hsame_trans (hsame_symm sameN1) sameNumerator)
                            sameN2
                        · exact hsame_trans (hsame_trans (hsame_symm sameD1) sameDenominator)
                            sameD2

end BEDC.Derived.RatUp
