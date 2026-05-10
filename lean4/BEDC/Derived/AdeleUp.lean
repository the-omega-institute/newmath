import BEDC.Derived.PadicUp
import BEDC.Derived.RealUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AdeleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
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

theorem AdeleHistoryCarrier_semanticNameCert :
    SemanticNameCert AdeleHistoryCarrier AdeleHistoryCarrier AdeleHistoryCarrier hsame := by
  have positiveDenominator : PositiveUnaryDenominator (BHist.e1 BHist.Empty) :=
    Iff.mpr PositiveUnaryDenominator_e1_iff_unary unary_empty
  have rationalCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    Iff.mpr RatHistoryCarrier_iff_positive_denominator positiveDenominator
  have carrierWitness :
      AdeleHistoryCarrier
        (append (BHist.e1 (BHist.e1 BHist.Empty))
          (BHist.e1 (BHist.e1 BHist.Empty))) :=
    AdeleHistoryCarrier_first_prime_unit_scale rationalCarrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro
          (append (BHist.e1 (BHist.e1 BHist.Empty))
            (BHist.e1 (BHist.e1 BHist.Empty)))
          carrierWitness
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same carrier
        cases carrier with
        | intro real rest =>
            cases rest with
            | intro p rest =>
                cases rest with
                | intro exponent rest =>
                    cases rest with
                    | intro result data =>
                        exact
                          ⟨real, p, exponent, result, data.left, data.right.left,
                            hsame_trans (hsame_symm same) data.right.right⟩
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

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

theorem AdeleHistoryCarrier_visible_zero_scale_result_nonempty {real p exponent result : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p (BHist.e0 exponent) result ->
      AdeleHistoryCarrier (append real result) ∧ (hsame result BHist.Empty -> False) := by
  intro realCarrier scale
  constructor
  · exact
      ⟨real, p, BHist.e0 exponent, result, realCarrier, scale,
        hsame_refl (append real result)⟩
  · intro resultEmpty
    have exponentEmpty : hsame (BHist.e0 exponent) BHist.Empty :=
      Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scale) resultEmpty
    exact not_hsame_e0_empty exponentEmpty

theorem AdeleHistoryCarrier_prime_swap_scale_readback {real p q r s : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p q r -> PadicPrimeScale q p s ->
      AdeleHistoryCarrier (append real r) ∧ AdeleHistoryCarrier (append real s) ∧
        hsame (append real r) (append real s) := by
  intro realCarrier left right
  have pUnary : UnaryHistory p := left.left.left
  have qUnary : UnaryHistory q := right.left.left
  have scaleSame : hsame r s :=
    PadicPrimeScale_prime_exponent_comm_hsame pUnary qUnary left right
  constructor
  · exact
      ⟨real, p, q, r, realCarrier, left, hsame_refl (append real r)⟩
  · constructor
    · exact
        ⟨real, q, p, s, realCarrier, right, hsame_refl (append real s)⟩
    · exact congrArg (append real) scaleSame

theorem AdeleHistoryCarrier_visible_scale_append_not_empty {real p exponent result : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p (BHist.e1 exponent) result ->
      hsame (append real result) BHist.Empty -> False := by
  intro _realCarrier scale appendEmpty
  have resultEmpty : hsame result BHist.Empty :=
    (append_eq_empty_iff.mp appendEmpty).right
  have exponentEmpty : hsame (BHist.e1 exponent) BHist.Empty :=
    Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scale) resultEmpty
  exact not_hsame_e1_empty exponentEmpty

theorem AdeleHistoryCarrier_visible_scale_append_result_hsame_transport {a a' s : BHist} :
    AdeleHistoryCarrier a -> (hsame (append a s) BHist.Empty -> False) ->
      hsame a a' -> hsame (append a' s) BHist.Empty -> False := by
  intro _carrier sourceNonempty sameAA' targetEmpty
  have appendSame : hsame (append a s) (append a' s) :=
    congrArg (fun x => append x s) sameAA'
  exact sourceNonempty (hsame_trans appendSame targetEmpty)

theorem AdeleHistoryCarrier_e1_real_append_nonempty {realTail p exponent result : BHist} :
    RealConstantHistoryCarrier (BHist.e1 realTail) -> PadicPrimeScale p exponent result ->
      AdeleHistoryCarrier (append (BHist.e1 realTail) result) ∧
        (hsame (append (BHist.e1 realTail) result) BHist.Empty -> False) := by
  intro realCarrier scale
  constructor
  · exact
      ⟨BHist.e1 realTail, p, exponent, result, realCarrier, scale,
        hsame_refl (append (BHist.e1 realTail) result)⟩
  · intro appendEmpty
    exact not_hsame_e1_empty (append_eq_empty_iff.mp appendEmpty).left

theorem AdeleHistoryCarrier_cont_result_nonempty {h k r : BHist} :
    AdeleHistoryCarrier h -> Cont h k r -> hsame r BHist.Empty -> False := by
  intro carrier continuation resultEmpty
  have emptyContinuation : Cont h k BHist.Empty :=
    cont_result_hsame_transport continuation resultEmpty
  have endpoints := cont_empty_result_inversion emptyContinuation
  cases endpoints.left
  exact AdeleHistoryCarrier_not_empty carrier (hsame_refl BHist.Empty)

theorem AdeleHistoryCarrier_cont_right_result_nonempty {h k r : BHist} :
    AdeleHistoryCarrier k -> Cont h k r -> hsame r BHist.Empty -> False := by
  intro carrier continuation resultEmpty
  have emptyContinuation : Cont h k BHist.Empty :=
    cont_result_hsame_transport continuation resultEmpty
  have endpoints := cont_empty_result_inversion emptyContinuation
  exact AdeleHistoryCarrier_not_empty carrier endpoints.right

theorem AdeleHistoryCarrier_cont_append_right_result_nonempty {h k p r : BHist} :
    AdeleHistoryCarrier k -> Cont h (append p k) r -> hsame r BHist.Empty -> False := by
  intro carrier continuation resultEmpty
  have emptyContinuation : Cont h (append p k) BHist.Empty :=
    cont_result_hsame_transport continuation resultEmpty
  have endpoints := cont_empty_result_inversion emptyContinuation
  have targetParts := append_eq_empty_iff.mp endpoints.right
  exact AdeleHistoryCarrier_not_empty carrier targetParts.right

theorem AdeleHistoryCarrier_visible_scale_cont_nonempty_package {real p exponent result k out : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p (BHist.e1 exponent) result ->
      Cont (append real result) k out ->
        AdeleHistoryCarrier (append real result) ∧
          (hsame result BHist.Empty -> False) ∧ (hsame out BHist.Empty -> False) := by
  intro realCarrier scale continuation
  have visibleScale :=
    AdeleHistoryCarrier_visible_scale_result_nonempty realCarrier scale
  exact And.intro visibleScale.left
    (And.intro visibleScale.right
      (AdeleHistoryCarrier_cont_result_nonempty visibleScale.left continuation))

theorem AdeleHistoryCarrier_visible_zero_scale_cont_nonempty_package
    {real p exponent result k out : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p (BHist.e0 exponent) result ->
      Cont (append real result) k out ->
        AdeleHistoryCarrier (append real result) ∧
          (hsame result BHist.Empty -> False) ∧ (hsame out BHist.Empty -> False) := by
  intro realCarrier scale continuation
  have visibleScale :=
    AdeleHistoryCarrier_visible_zero_scale_result_nonempty realCarrier scale
  exact And.intro visibleScale.left
    (And.intro visibleScale.right
      (AdeleHistoryCarrier_cont_result_nonempty visibleScale.left continuation))

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

theorem AdeleRealStreamPrefix_long_prefix_visible_scale_carrier {x y : Nat -> BHist}
    {n m : Nat} {denTail imagTail exponent result : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale (BHist.e1 (BHist.e1 BHist.Empty)) exponent result ->
          RealStreamPrefixClassifier x y n ∧
            AdeleHistoryCarrier (append (BHist.e1 (BHist.e1 denTail)) result) := by
  intro classified sameReal sameImag scale
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have visible :=
    RealStreamPrefixClassifier_e1_pair_readback prefixAtN sameReal sameImag
  have denUnary : UnaryHistory denTail :=
    unary_e1_inversion visible.left
  have realTailCarrier : RatHistoryCarrier (BHist.e1 denTail) :=
    RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr denUnary)
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 (BHist.e1 denTail)) :=
    Iff.mpr RealConstantHistoryCarrier_e1_iff_rat realTailCarrier
  constructor
  · exact prefixAtN
  · exact
      ⟨BHist.e1 (BHist.e1 denTail), BHist.e1 (BHist.e1 BHist.Empty), exponent, result,
        realCarrier, scale,
        hsame_refl (append (BHist.e1 (BHist.e1 denTail)) result)⟩

theorem AdeleRealStreamPrefix_long_prefix_visible_padic_scale_carrier {x y : Nat -> BHist}
    {n m : Nat} {denTail imagTail p exponent result : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale p exponent result ->
          RealStreamPrefixClassifier x y n ∧
            AdeleHistoryCarrier (append (BHist.e1 (BHist.e1 denTail)) result) := by
  intro classified sameReal sameImag scale
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have visible :=
    RealStreamPrefixClassifier_e1_pair_readback prefixAtN sameReal sameImag
  have denUnary : UnaryHistory denTail :=
    unary_e1_inversion visible.left
  have realTailCarrier : RatHistoryCarrier (BHist.e1 denTail) :=
    RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr denUnary)
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 (BHist.e1 denTail)) :=
    Iff.mpr RealConstantHistoryCarrier_e1_iff_rat realTailCarrier
  constructor
  · exact prefixAtN
  · exact
      ⟨BHist.e1 (BHist.e1 denTail), p, exponent, result, realCarrier, scale,
        hsame_refl (append (BHist.e1 (BHist.e1 denTail)) result)⟩

theorem AdeleRealStreamPrefix_long_prefix_visible_unit_scale_readback {x y : Nat -> BHist}
    {n m : Nat} {denTail imagTail p result : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale p (BHist.e1 BHist.Empty) result ->
          RealStreamPrefixClassifier x y n ∧
            AdeleHistoryCarrier (append (BHist.e1 (BHist.e1 denTail)) result) ∧
              hsame (append (BHist.e1 (BHist.e1 denTail)) result)
                (append (BHist.e1 (BHist.e1 denTail)) p) := by
  intro classified sameReal sameImag scale
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have visible :=
    RealStreamPrefixClassifier_e1_pair_readback prefixAtN sameReal sameImag
  have denUnary : UnaryHistory denTail :=
    unary_e1_inversion visible.left
  have realTailCarrier : RatHistoryCarrier (BHist.e1 denTail) :=
    RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr denUnary)
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 (BHist.e1 denTail)) :=
    Iff.mpr RealConstantHistoryCarrier_e1_iff_rat realTailCarrier
  have resultPrime : hsame result p :=
    PadicPrimeScale_unit_exponent_result_prime_hsame scale
  exact And.intro prefixAtN
    (And.intro
      ⟨BHist.e1 (BHist.e1 denTail), p, BHist.e1 BHist.Empty, result, realCarrier,
        scale, hsame_refl (append (BHist.e1 (BHist.e1 denTail)) result)⟩
      (congrArg (append (BHist.e1 (BHist.e1 denTail))) resultPrime))

theorem AdeleRealStreamPrefix_long_prefix_visible_scale_result_nonempty {x y : Nat -> BHist}
    {n m : Nat} {denTail imagTail exponent result : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e1 exponent) result ->
          RealStreamPrefixClassifier x y n ∧
            AdeleHistoryCarrier (append (BHist.e1 (BHist.e1 denTail)) result) ∧
              (hsame result BHist.Empty -> False) := by
  intro classified sameReal sameImag scale
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have visible :=
    RealStreamPrefixClassifier_e1_pair_readback prefixAtN sameReal sameImag
  have denUnary : UnaryHistory denTail :=
    unary_e1_inversion visible.left
  have realTailCarrier : RatHistoryCarrier (BHist.e1 denTail) :=
    RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr denUnary)
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 (BHist.e1 denTail)) :=
    Iff.mpr RealConstantHistoryCarrier_e1_iff_rat realTailCarrier
  have visibleScale :=
    AdeleHistoryCarrier_visible_scale_result_nonempty realCarrier scale
  exact And.intro prefixAtN visibleScale

theorem AdeleRealStreamPrefix_long_prefix_visible_zero_scale_result_nonempty {x y : Nat -> BHist}
    {n m : Nat} {denTail imagTail exponent result : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e0 exponent) result ->
          RealStreamPrefixClassifier x y n ∧
            AdeleHistoryCarrier (append (BHist.e1 (BHist.e1 denTail)) result) ∧
              (hsame result BHist.Empty -> False) := by
  intro classified sameReal sameImag scale
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have visible :=
    RealStreamPrefixClassifier_e1_pair_readback prefixAtN sameReal sameImag
  have denUnary : UnaryHistory denTail :=
    unary_e1_inversion visible.left
  have realTailCarrier : RatHistoryCarrier (BHist.e1 denTail) :=
    RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr denUnary)
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 (BHist.e1 denTail)) :=
    Iff.mpr RealConstantHistoryCarrier_e1_iff_rat realTailCarrier
  have visibleScale :=
    AdeleHistoryCarrier_visible_zero_scale_result_nonempty realCarrier scale
  exact And.intro prefixAtN visibleScale

theorem AdeleRealStreamPrefix_long_prefix_visible_scale_cont_result_nonempty {x y : Nat -> BHist}
    {n m : Nat} {denTail imagTail exponent result k out : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e1 exponent) result ->
          Cont (append (BHist.e1 (BHist.e1 denTail)) result) k out ->
            hsame out BHist.Empty -> False := by
  intro classified sameReal sameImag scale continuation outEmpty
  have visibleScale :=
    AdeleRealStreamPrefix_long_prefix_visible_scale_result_nonempty
      classified sameReal sameImag scale
  exact AdeleHistoryCarrier_cont_result_nonempty visibleScale.right.left continuation outEmpty

theorem AdeleRealStreamPrefix_long_prefix_visible_scale_append_not_empty {x y : Nat -> BHist}
    {n m : Nat} {denTail imagTail exponent result : BHist} :
    RealStreamPrefixClassifier x y (m + n) ->
      hsame (x n) (BHist.e1 (BHist.e1 denTail)) -> hsame (y n) (BHist.e1 imagTail) ->
        PadicPrimeScale (BHist.e1 (BHist.e1 BHist.Empty)) exponent result ->
          hsame (append (BHist.e1 (BHist.e1 denTail)) result) BHist.Empty -> False := by
  intro classified sameReal sameImag scale appendEmpty
  have carrier :=
    (AdeleRealStreamPrefix_long_prefix_visible_scale_carrier classified sameReal sameImag scale).right
  exact AdeleHistoryCarrier_not_empty carrier appendEmpty

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

theorem AdeleHistoryCarrier_unit_scale_real_prime_readback {real p result : BHist} :
    RealConstantHistoryCarrier real -> PadicPrimeScale p (BHist.e1 BHist.Empty) result ->
      AdeleHistoryCarrier (append real result) ∧ hsame (append real result) (append real p) := by
  intro realCarrier scale
  have resultPrime : hsame result p :=
    PadicPrimeScale_unit_exponent_result_prime_hsame scale
  constructor
  · exact
      ⟨real, p, BHist.e1 BHist.Empty, result, realCarrier, scale,
        hsame_refl (append real result)⟩
  · exact congrArg (append real) resultPrime

theorem AdeleHistoryCarrier_unit_left_scale_cont_readback {real p q result : BHist} :
    RealConstantHistoryCarrier real -> UnaryHistory q ->
      PadicPrimeScale p (append (BHist.e1 BHist.Empty) q) result ->
        AdeleHistoryCarrier (append real result) ∧
          ∃ e : BHist, PadicPrimeScale p q e ∧ Cont p e result := by
  intro realCarrier unaryQ scale
  have factorization :=
    Iff.mp (PadicPrimeScale_append_unit_left_factorization_iff (p := p) (q := q)
      (r := result) unaryQ) scale
  exact And.intro
    ⟨real, p, append (BHist.e1 BHist.Empty) q, result, realCarrier, scale,
      hsame_refl (append real result)⟩
    factorization

theorem AdeleHistoryCarrier_unit_left_scale_append_readback {real p q result : BHist} :
    RealConstantHistoryCarrier real -> UnaryHistory q ->
      PadicPrimeScale p (append (BHist.e1 BHist.Empty) q) result ->
        AdeleHistoryCarrier (append real result) ∧
          Exists (fun e : BHist => PadicPrimeScale p q e ∧
            hsame (append real result) (append real (append p e))) := by
  intro realCarrier unaryQ scale
  have factorization :=
    Iff.mp (PadicPrimeScale_append_unit_left_factorization_iff (p := p) (q := q)
      (r := result) unaryQ) scale
  cases factorization with
  | intro e data =>
      exact And.intro
        ⟨real, p, append (BHist.e1 BHist.Empty) q, result, realCarrier, scale,
          hsame_refl (append real result)⟩
        (Exists.intro e (And.intro data.left (congrArg (append real) data.right)))

theorem AdeleHistoryCarrier_unit_right_scale_cont_readback {real p w result : BHist} :
    RealConstantHistoryCarrier real -> UnaryHistory w ->
      PadicPrimeScale p (append w (BHist.e1 BHist.Empty)) result ->
        AdeleHistoryCarrier (append real result) ∧
          ∃ n : BHist, PadicPrimeScale p w n ∧ Cont n p result := by
  intro realCarrier unaryW scale
  have factorization :=
    Iff.mp (PadicPrimeScale_append_unit_right_factorization_iff (p := p) (w := w)
      (r := result) unaryW) scale
  exact And.intro
    ⟨real, p, append w (BHist.e1 BHist.Empty), result, realCarrier, scale,
      hsame_refl (append real result)⟩
    factorization

theorem AdeleHistoryCarrier_unit_right_scale_append_readback {real p w result : BHist} :
    RealConstantHistoryCarrier real -> UnaryHistory w ->
      PadicPrimeScale p (append w (BHist.e1 BHist.Empty)) result ->
        AdeleHistoryCarrier (append real result) ∧
          Exists (fun n : BHist => PadicPrimeScale p w n ∧
            hsame (append real result) (append real (append n p))) := by
  intro realCarrier unaryW scale
  have readback :=
    AdeleHistoryCarrier_unit_right_scale_cont_readback realCarrier unaryW scale
  cases readback.right with
  | intro n data =>
      exact And.intro readback.left
        (Exists.intro n (And.intro data.left (congrArg (append real) data.right)))

theorem AdeleUp_StdBridge {real p exponent result h endpoint : BHist} :
    RealConstantHistoryCarrier real ->
      PadicPrimeScale p exponent result ->
        hsame h (append real result) ->
          Cont h BHist.Empty endpoint ->
            SemanticNameCert AdeleHistoryCarrier AdeleHistoryCarrier AdeleHistoryCarrier hsame ∧
              AdeleHistoryCarrier h ∧ AdeleHistoryCarrier endpoint ∧ hsame endpoint h ∧
                (hsame endpoint BHist.Empty -> False) := by
  intro realCarrier scale sameH continuation
  have carrierH : AdeleHistoryCarrier h :=
    ⟨real, p, exponent, result, realCarrier, scale, sameH⟩
  have sameEndpointH : hsame endpoint h :=
    Iff.mp cont_right_unit_iff continuation
  have carrierEndpoint : AdeleHistoryCarrier endpoint :=
    AdeleHistoryCarrier_semanticNameCert.core.carrier_respects_equiv
      (hsame_symm sameEndpointH) carrierH
  have endpointNonempty : hsame endpoint BHist.Empty -> False :=
    AdeleHistoryCarrier_cont_result_nonempty carrierH continuation
  exact
    ⟨AdeleHistoryCarrier_semanticNameCert, carrierH, carrierEndpoint, sameEndpointH,
      endpointNonempty⟩

end BEDC.Derived.AdeleUp
