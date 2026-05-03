import BEDC.Derived.PadicUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.AdeleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.PadicUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

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

end BEDC.Derived.AdeleUp
