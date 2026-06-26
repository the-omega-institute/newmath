import BEDC.Derived.ContFracUp
import BEDC.Derived.PrimeUp.UnitResult

namespace BEDC.Derived.ContFracBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.IntUp
open BEDC.Derived.GcdUp
open BEDC.Derived.ContFracUp

def NatConvergentPairCarrier (c : ConvergentPair BHist) : Prop :=
  UnaryHistory c.p ∧ UnaryHistory c.q

def NatConvergentStateCarrier (s : ConvergentState BHist) : Prop :=
  NatConvergentPairCarrier s.prev ∧ NatConvergentPairCarrier s.curr

def NatConvergentPositiveDet (s : ConvergentState BHist) : Prop :=
  Cont NatOne (natMulFn s.prev.p s.curr.q) (natMulFn s.curr.p s.prev.q)

def NatConvergentNegativeDet (s : ConvergentState BHist) : Prop :=
  Cont NatOne (natMulFn s.curr.p s.prev.q) (natMulFn s.prev.p s.curr.q)

def NatConvergentUnitDet (s : ConvergentState BHist) : Prop :=
  NatConvergentPositiveDet s ∨ NatConvergentNegativeDet s

def adjacentConvergentGapDenominator (s : ConvergentState BHist) : BHist :=
  natMulFn s.curr.q s.prev.q

def AdjacentConvergentGapBound (s : ConvergentState BHist) : Prop :=
  NatConvergentUnitDet s ∧
    NatMul s.curr.q s.prev.q (adjacentConvergentGapDenominator s)

def natConvergentStep (a : BHist) (s : ConvergentState BHist) :
    ConvergentState BHist :=
  { prev := s.curr
    curr :=
      { p := append (natMulFn a s.curr.p) s.prev.p
        q := append (natMulFn a s.curr.q) s.prev.q } }

def natConvergentStateFrom :
    ConvergentState BHist -> List BHist -> ConvergentState BHist
  | s, [] => s
  | s, a :: tail => natConvergentStateFrom (natConvergentStep a s) tail

def natInitialConvergentState : ConvergentState BHist :=
  { prev := { p := BHist.Empty, q := NatOne }
    curr := { p := NatOne, q := BHist.Empty } }

def natConvergentStateOfList (coeffs : List BHist) : ConvergentState BHist :=
  natConvergentStateFrom natInitialConvergentState coeffs

theorem natInitialConvergentState_carrier :
    NatConvergentStateCarrier natInitialConvergentState := by
  unfold NatConvergentStateCarrier NatConvergentPairCarrier natInitialConvergentState
  exact ⟨⟨unary_empty, unary_e1_closed unary_empty⟩,
    ⟨unary_e1_closed unary_empty, unary_empty⟩⟩

theorem natConvergentStep_carrier {a : BHist} {s : ConvergentState BHist} :
    UnaryHistory a -> NatConvergentStateCarrier s ->
      NatConvergentStateCarrier (natConvergentStep a s) := by
  intro aUnary carrier
  unfold NatConvergentStateCarrier NatConvergentPairCarrier natConvergentStep
  constructor
  · exact carrier.right
  · constructor
    · exact unary_append_closed
        (natMulFn_unary aUnary carrier.right.left) carrier.left.left
    · exact unary_append_closed
        (natMulFn_unary aUnary carrier.right.right) carrier.left.right

theorem natConvergentStateFrom_carrier {s : ConvergentState BHist}
    {coeffs : List BHist} :
    (forall a : BHist, a ∈ coeffs -> UnaryHistory a) ->
      NatConvergentStateCarrier s ->
        NatConvergentStateCarrier (natConvergentStateFrom s coeffs) := by
  intro coeffUnary carrier
  induction coeffs generalizing s with
  | nil =>
      exact carrier
  | cons a tail ih =>
      unfold natConvergentStateFrom
      apply ih
      · intro b hb
        exact coeffUnary b (List.Mem.tail a hb)
      · exact natConvergentStep_carrier
          (coeffUnary a (List.Mem.head tail)) carrier

theorem natConvergentStateOfList_carrier {coeffs : List BHist} :
    (forall a : BHist, a ∈ coeffs -> UnaryHistory a) ->
      NatConvergentStateCarrier (natConvergentStateOfList coeffs) := by
  intro coeffUnary
  unfold natConvergentStateOfList
  exact natConvergentStateFrom_carrier coeffUnary natInitialConvergentState_carrier

theorem adjacentConvergentGap_bound_certificate {s : ConvergentState BHist} :
    NatConvergentStateCarrier s -> NatConvergentUnitDet s ->
      AdjacentConvergentGapBound s := by
  intro carrier unitDet
  unfold AdjacentConvergentGapBound adjacentConvergentGapDenominator
  exact ⟨unitDet, natMulFn_rel carrier.right.right carrier.left.right⟩

private theorem current_denominator_nonempty_for_divisor {s : ConvergentState BHist}
    {d : BHist} :
    (hsame s.curr.q BHist.Empty -> False) ->
      NatDivides d s.curr.q ->
        (hsame d BHist.Empty -> False) := by
  intro qNonempty dividesQ dEmpty
  have emptyDividesQ : NatDivides BHist.Empty s.curr.q :=
    (NatDivides_divisor_hsame_transport dividesQ dEmpty).right
  exact qNonempty (NatDivides_empty_left_result_empty emptyDividesQ)

private theorem common_divisor_divides_one_of_positive_det
    {s : ConvergentState BHist} {d : BHist} :
    NatConvergentStateCarrier s ->
      (hsame s.curr.q BHist.Empty -> False) ->
        NatConvergentPositiveDet s ->
          NatDivides d s.curr.p -> NatDivides d s.curr.q ->
            NatDivides d NatOne := by
  intro carrier qNonempty positiveDet dividesP dividesQ
  have dUnary : UnaryHistory d := NatDivides_divisor_unary dividesQ
  have dNonempty : hsame d BHist.Empty -> False :=
    current_denominator_nonempty_for_divisor qNonempty dividesQ
  have leftMul :
      NatMul s.curr.p s.prev.q (natMulFn s.curr.p s.prev.q) :=
    natMulFn_rel carrier.right.left carrier.left.right
  have rightMul :
      NatMul s.prev.p s.curr.q (natMulFn s.prev.p s.curr.q) :=
    natMulFn_rel carrier.left.left carrier.right.right
  have dDividesLeft :
      NatDivides d (natMulFn s.curr.p s.prev.q) :=
    NatDivides_mul_right_factor_closed carrier.left.right dividesP leftMul
  have dDividesRight :
      NatDivides d (natMulFn s.prev.p s.curr.q) :=
    NatDivides_mul_left_closed carrier.left.left dividesQ rightMul
  have leftUnary : UnaryHistory (natMulFn s.curr.p s.prev.q) :=
    natMulFn_unary carrier.right.left carrier.left.right
  have rightUnary : UnaryHistory (natMulFn s.prev.p s.curr.q) :=
    natMulFn_unary carrier.left.left carrier.right.right
  exact NatDivides_cont_left_factor dUnary dNonempty
    (unary_e1_closed unary_empty) rightUnary leftUnary
    dDividesRight dDividesLeft positiveDet

private theorem common_divisor_divides_one_of_negative_det
    {s : ConvergentState BHist} {d : BHist} :
    NatConvergentStateCarrier s ->
      (hsame s.curr.q BHist.Empty -> False) ->
        NatConvergentNegativeDet s ->
          NatDivides d s.curr.p -> NatDivides d s.curr.q ->
            NatDivides d NatOne := by
  intro carrier qNonempty negativeDet dividesP dividesQ
  have dUnary : UnaryHistory d := NatDivides_divisor_unary dividesQ
  have dNonempty : hsame d BHist.Empty -> False :=
    current_denominator_nonempty_for_divisor qNonempty dividesQ
  have leftMul :
      NatMul s.curr.p s.prev.q (natMulFn s.curr.p s.prev.q) :=
    natMulFn_rel carrier.right.left carrier.left.right
  have rightMul :
      NatMul s.prev.p s.curr.q (natMulFn s.prev.p s.curr.q) :=
    natMulFn_rel carrier.left.left carrier.right.right
  have dDividesLeft :
      NatDivides d (natMulFn s.curr.p s.prev.q) :=
    NatDivides_mul_right_factor_closed carrier.left.right dividesP leftMul
  have dDividesRight :
      NatDivides d (natMulFn s.prev.p s.curr.q) :=
    NatDivides_mul_left_closed carrier.left.left dividesQ rightMul
  have leftUnary : UnaryHistory (natMulFn s.curr.p s.prev.q) :=
    natMulFn_unary carrier.right.left carrier.left.right
  have rightUnary : UnaryHistory (natMulFn s.prev.p s.curr.q) :=
    natMulFn_unary carrier.left.left carrier.right.right
  exact NatDivides_cont_left_factor dUnary dNonempty
    (unary_e1_closed unary_empty) leftUnary rightUnary
    dDividesLeft dDividesRight negativeDet

theorem common_divisor_divides_one_of_unit_det
    {s : ConvergentState BHist} {d : BHist} :
    NatConvergentStateCarrier s ->
      (hsame s.curr.q BHist.Empty -> False) ->
        NatConvergentUnitDet s ->
          NatDivides d s.curr.p -> NatDivides d s.curr.q ->
            NatDivides d NatOne := by
  intro carrier qNonempty unitDet dividesP dividesQ
  cases unitDet with
  | inl positiveDet =>
      exact common_divisor_divides_one_of_positive_det
        carrier qNonempty positiveDet dividesP dividesQ
  | inr negativeDet =>
      exact common_divisor_divides_one_of_negative_det
        carrier qNonempty negativeDet dividesP dividesQ

theorem convergentState_natCoprime {s : ConvergentState BHist} :
    NatConvergentStateCarrier s ->
      (hsame s.curr.q BHist.Empty -> False) ->
        NatConvergentUnitDet s ->
          NatGcd s.curr.p s.curr.q NatOne := by
  intro carrier qNonempty unitDet
  constructor
  · exact carrier.right.left
  · constructor
    · exact carrier.right.right
    · constructor
      · exact unary_e1_closed unary_empty
      · constructor
        · exact (NatDivides_reflexive_pair carrier.right.left).left
        · constructor
          · exact (NatDivides_reflexive_pair carrier.right.right).left
          · intro d dividesP dividesQ
            exact common_divisor_divides_one_of_unit_det
              carrier qNonempty unitDet dividesP dividesQ

theorem convergentState_natGcdFn_unit {s : ConvergentState BHist} :
    NatConvergentStateCarrier s ->
      (hsame s.curr.q BHist.Empty -> False) ->
        NatConvergentUnitDet s ->
          hsame (natGcdFn s.curr.p s.curr.q) NatOne := by
  intro carrier qNonempty unitDet
  exact NatGcd_unique_hsame
    (natGcdFn_spec carrier.right.left carrier.right.right)
    (convergentState_natCoprime carrier qNonempty unitDet)

private theorem nat_one_le_of_pos {n : Nat} :
    0 < n -> 1 ≤ n := by
  intro positive
  exact Nat.succ_le_of_lt positive

theorem convergentStep_denominator_monotone
    (a : BHist) (s : ConvergentState BHist) :
    UnaryHistory a -> (hsame a BHist.Empty -> False) ->
      NatConvergentStateCarrier s ->
        bwordLength s.curr.q ≤ bwordLength (natConvergentStep a s).curr.q := by
  intro aUnary aNonempty carrier
  unfold natConvergentStep
  have aPositive : 0 < bwordLength a :=
    NatUnary_nonempty_length_pos aUnary aNonempty
  have oneLeA : 1 ≤ bwordLength a := nat_one_le_of_pos aPositive
  have currLeProduct :
      bwordLength s.curr.q ≤ bwordLength a * bwordLength s.curr.q := by
    calc
      bwordLength s.curr.q = 1 * bwordLength s.curr.q := by
        rw [Nat.one_mul]
      _ ≤ bwordLength a * bwordLength s.curr.q :=
        Nat.mul_le_mul_right (bwordLength s.curr.q) oneLeA
  have productLeNext :
      bwordLength a * bwordLength s.curr.q ≤
        bwordLength a * bwordLength s.curr.q + bwordLength s.prev.q :=
    Nat.le.intro rfl
  rw [bwordLength_append]
  rw [natMulFn_bwordLength aUnary carrier.right.right]
  exact Nat.le_trans currLeProduct productLeNext

theorem integerConvergents_alternating_determinant
    (coeffs : List ContFracUp.IntegerUp) :
    IntEq (integerConvergentDet (integerConvergentStateOfList coeffs))
      (Rel.alternatingOne BEDC.Algebra.Rel.IntegerUp_RelCommRing coeffs.length) :=
  integerContFracConvergents_det coeffs

end BEDC.Derived.ContFracBoundUp
