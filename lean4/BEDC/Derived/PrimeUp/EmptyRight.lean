import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatMul_empty_right_iff {d n : BHist} :
    NatMul d BHist.Empty n ↔ UnaryHistory d ∧ hsame n BHist.Empty := by
  constructor
  · intro mul
    cases mul with
    | zero hd =>
        constructor
        · exact hd
        · rfl
  · intro data
    cases data with
    | intro hd sameN =>
        cases sameN
        exact NatMul.zero hd

end BEDC.Derived.PrimeUp
