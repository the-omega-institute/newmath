import BEDC.Derived.PadicUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.AdeleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.PadicUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

def AdeleHistoryCarrier (h : BHist) : Prop :=
  ∃ real : BHist, ∃ p : BHist, ∃ exponent : BHist, ∃ result : BHist,
    RealConstantHistoryCarrier real ∧ PadicPrimeScale p exponent result ∧
      hsame h (append real result)

theorem AdeleHistoryCarrier_not_empty {h : BHist} :
    AdeleHistoryCarrier h -> hsame h BHist.Empty -> False := by
  intro carrier emptyH
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro _p rest =>
          cases rest with
          | intro _exponent rest =>
              cases rest with
              | intro result data =>
                  have appendEmpty : hsame (append real result) BHist.Empty :=
                    hsame_trans (hsame_symm data.right.right) emptyH
                  have emptyParts := append_eq_empty_iff.mp appendEmpty
                  cases data.left with
                  | intro witness realData =>
                      exact not_hsame_emp_e1
                        (hsame_trans (hsame_symm emptyParts.left) realData.left)

theorem AdeleRealPadic_e1_real_nonempty_scale_result_package
    {realTail p exponent result : BHist} :
    RatHistoryCarrier realTail ->
    PadicPrimeScale p (BHist.e1 exponent) result ->
      RealConstantHistoryCarrier (BHist.e1 realTail) ∧
        (hsame result BHist.Empty -> False) := by
  intro ratCarrier scale
  constructor
  · exact Iff.mpr RealConstantHistoryCarrier_e1_iff_rat ratCarrier
  · intro resultEmpty
    have exponentEmpty : hsame (BHist.e1 exponent) BHist.Empty :=
      Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scale) resultEmpty
    exact not_hsame_e1_empty exponentEmpty

theorem AdeleHistoryCarrier_first_prime_unit_scale {realTail : BHist} :
    RatHistoryCarrier realTail ->
      AdeleHistoryCarrier
        (append (BHist.e1 realTail) (BHist.e1 (BHist.e1 BHist.Empty))) := by
  intro ratCarrier
  exact
    ⟨BHist.e1 realTail, BHist.e1 (BHist.e1 BHist.Empty), BHist.e1 BHist.Empty,
      BHist.e1 (BHist.e1 BHist.Empty),
      Iff.mpr RealConstantHistoryCarrier_e1_iff_rat ratCarrier,
      PadicPrimeScale_first_prime_unit_exponent_result,
      hsame_refl (append (BHist.e1 realTail) (BHist.e1 (BHist.e1 BHist.Empty)))⟩

theorem AdeleHistoryCarrier_visible_scale_result_nonempty {real p exponent result : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p (BHist.e1 exponent) result ->
      AdeleHistoryCarrier (append real result) ∧ (hsame result BHist.Empty -> False) := by
  intro realCarrier scale
  constructor
  · exact
      ⟨real, p, BHist.e1 exponent, result, realCarrier, scale,
        hsame_refl (append real result)⟩
  · intro resultEmpty
    have exponentEmpty : hsame (BHist.e1 exponent) BHist.Empty :=
      Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scale) resultEmpty
    exact not_hsame_e1_empty exponentEmpty

theorem AdeleHistoryCarrier_visible_scale_append_not_empty {real p exponent result : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p (BHist.e1 exponent) result ->
      hsame (append real result) BHist.Empty -> False := by
  intro _realCarrier scale appendEmpty
  have resultEmpty : hsame result BHist.Empty :=
    (append_eq_empty_iff.mp appendEmpty).right
  have exponentEmpty : hsame (BHist.e1 exponent) BHist.Empty :=
    Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scale) resultEmpty
  exact not_hsame_e1_empty exponentEmpty

theorem AdeleRealStreamPrefix_visible_scale_carrier {x y : Nat -> BHist} {n m : Nat}
    {denTail imagTail exponent result : BHist} :
    (forall i : Nat, UnaryHistory (x i)) -> RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale (BHist.e1 (BHist.e1 BHist.Empty)) exponent result ->
          RealStreamPrefixClassifier x y n ∧
            AdeleHistoryCarrier (append (BHist.e1 (BHist.e1 denTail)) result) := by
  intro unary classified sameReal sameImag scale
  have prefixData := RealStreamPrefixClassifier_add_left_previous_with_unary unary n m classified
  have visible :=
    RealStreamPrefixClassifier_e1_pair_readback prefixData.left sameReal sameImag
  have denUnary : UnaryHistory denTail :=
    unary_e1_inversion visible.left
  have realTailCarrier : RatHistoryCarrier (BHist.e1 denTail) :=
    RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr denUnary)
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 (BHist.e1 denTail)) :=
    Iff.mpr RealConstantHistoryCarrier_e1_iff_rat realTailCarrier
  constructor
  · exact prefixData.left
  · exact
      ⟨BHist.e1 (BHist.e1 denTail), BHist.e1 (BHist.e1 BHist.Empty), exponent, result,
        realCarrier, scale,
        hsame_refl (append (BHist.e1 (BHist.e1 denTail)) result)⟩

theorem AdeleRealPadic_e1_append_empty_padic_result_iff {p w q d e n r out : BHist} :
    RealConstantHistoryCarrier (BHist.e1 d) -> PadicPrimeScale p w n ->
      RealConstantHistoryCarrier (BHist.e1 e) -> PadicPrimeScale p q r -> Cont n r out ->
        (hsame out BHist.Empty <->
          RatHistoryCarrier d ∧ RatHistoryCarrier e ∧ hsame w BHist.Empty ∧
            hsame q BHist.Empty) := by
  intro realD left realE right continuation
  have ratD : RatHistoryCarrier d :=
    Iff.mp RealConstantHistoryCarrier_e1_iff_rat realD
  have ratE : RatHistoryCarrier e :=
    Iff.mp RealConstantHistoryCarrier_e1_iff_rat realE
  have padicEmpty :=
    PadicPrimeScale_append_empty_result_empty_factors_iff left right continuation
  constructor
  · intro outEmpty
    have factorsEmpty := Iff.mp padicEmpty outEmpty
    exact And.intro ratD (And.intro ratE (And.intro factorsEmpty.left factorsEmpty.right))
  · intro data
    exact Iff.mpr padicEmpty (And.intro data.right.right.left data.right.right.right)

theorem AdeleConstantSliceCarrier_hsame_transport {h h' : BHist} :
    (let AdeleConstantSliceCarrier : BHist -> Prop := fun x =>
      ∃ d : BHist, ∃ p : BHist, ∃ exponent : BHist, ∃ result : BHist,
        hsame x (BHist.e1 d) ∧ RatHistoryCarrier d ∧
          PadicPrimeScale p exponent result;
      hsame h h' -> AdeleConstantSliceCarrier h -> AdeleConstantSliceCarrier h') := by
  exact fun sameHH' carrier =>
    match carrier with
    | ⟨d, p, exponent, result, sameH, ratCarrier, scale⟩ =>
        ⟨d, p, exponent, result, hsame_trans (hsame_symm sameHH') sameH, ratCarrier, scale⟩

theorem AdeleHistoryCarrier_empty_scale_real_readback {real p result : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p BHist.Empty result ->
      AdeleHistoryCarrier (append real result) ∧ hsame (append real result) real := by
  intro realCarrier scale
  have resultEmpty : hsame result BHist.Empty :=
    Iff.mpr (PadicPrimeScale_empty_result_iff_empty_exponent scale)
      (hsame_refl BHist.Empty)
  constructor
  · exact
      ⟨real, p, BHist.Empty, result, realCarrier, scale,
        hsame_refl (append real result)⟩
  · exact hsame_trans (congrArg (append real) resultEmpty) (append_empty_right real)

end BEDC.Derived.AdeleUp
