import BEDC.Derived.PadicUp

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem PadicPrimeScale_append_factor_empty_alignment_iff {p w q n e r : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      (hsame n BHist.Empty ∧ hsame e BHist.Empty ∧ hsame r BHist.Empty ↔
        hsame w BHist.Empty ∧ hsame q BHist.Empty) := by
  intro left right continuation
  have leftIff := PadicPrimeScale_empty_result_iff_empty_exponent left
  have rightIff := PadicPrimeScale_empty_result_iff_empty_exponent right
  have resultIff :=
    PadicPrimeScale_append_empty_result_empty_factors_iff left right continuation
  constructor
  · intro alignment
    exact And.intro (Iff.mp leftIff alignment.left) (Iff.mp rightIff alignment.right.left)
  · intro factors
    exact And.intro
      (Iff.mpr leftIff factors.left)
      (And.intro
        (Iff.mpr rightIff factors.right)
        (Iff.mpr resultIff factors))

end BEDC.Derived.PadicUp
