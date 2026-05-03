import BEDC.Derived.RealUp
import BEDC.Derived.PadicUp

namespace BEDC.Derived.AdeleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.PadicUp

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

end BEDC.Derived.AdeleUp
