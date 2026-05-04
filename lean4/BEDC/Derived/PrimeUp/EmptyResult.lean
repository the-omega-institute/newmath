import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatMul_succ_result_empty_left_empty_iff {d q n : BHist} :
    NatMul d (BHist.e1 q) n -> (hsame n BHist.Empty ↔ hsame d BHist.Empty) := by
  intro mul
  constructor
  · intro resultEmpty
    exact NatMul_succ_result_empty_left_empty mul resultEmpty
  · intro dEmpty
    cases dEmpty
    exact NatMul_empty_left_result_empty mul

theorem NatDivides_empty_left_iff {n : BHist} :
    NatDivides BHist.Empty n ↔ hsame n BHist.Empty := by
  constructor
  · intro divides
    exact NatDivides_empty_left_result_empty divides
  · intro nEmpty
    cases nEmpty
    exact (NatDivides_empty_right_iff (d := BHist.Empty)).mpr unary_empty

end BEDC.Derived.PrimeUp
