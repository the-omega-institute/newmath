import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem PadicPrimeScale_append_cont_closure {p w q n e r : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      PadicPrimeScale p (append w q) r := by
  intro left right continuation
  exact And.intro left.left (NatMul_append_cont left.right right.right continuation)

theorem PadicPrimeScale_append_empty_result_empty_factors_iff {p w q n e r : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r ->
      (hsame r BHist.Empty <-> hsame w BHist.Empty ∧ hsame q BHist.Empty) := by
  intro left right continuation
  have combined : PadicPrimeScale p (append w q) r :=
    PadicPrimeScale_append_cont_closure left right continuation
  have resultIff := PadicPrimeScale_empty_result_iff_empty_exponent combined
  constructor
  · intro resultEmpty
    exact append_eq_empty_iff.mp (Iff.mp resultIff resultEmpty)
  · intro partsEmpty
    exact Iff.mpr resultIff (append_eq_empty_iff.mpr partsEmpty)

end BEDC.Derived.PadicUp
