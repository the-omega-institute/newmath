import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

def PadicPrimeScale (p exponent result : BHist) : Prop :=
  NatPrime p ∧ NatMul p exponent result

theorem PadicPrimeScale_empty_result_iff_empty_exponent {p exponent result : BHist} :
    PadicPrimeScale p exponent result ->
      (hsame result BHist.Empty ↔ hsame exponent BHist.Empty) := by
  intro scale
  constructor
  · intro resultEmpty
    have primeNonempty : hsame p BHist.Empty -> False := by
      intro primeEmpty
      cases primeEmpty
      exact NatUnaryStrictPrefix_empty_right_absurd scale.left.right.left
    cases resultEmpty
    exact Iff.mp
      (NatMul_nonempty_multiplicand_empty_result_iff scale.left.left primeNonempty)
      scale.right
  · intro exponentEmpty
    cases exponentEmpty
    cases scale.right with
    | zero _unary =>
        rfl

end BEDC.Derived.PadicUp
