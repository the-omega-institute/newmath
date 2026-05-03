import BEDC.Derived.PadicUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.AdeleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

end BEDC.Derived.AdeleUp
