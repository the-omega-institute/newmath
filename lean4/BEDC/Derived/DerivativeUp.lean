import BEDC.Derived.ComplexDiffUp

namespace BEDC.Derived.DerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp

theorem DerivativeCplxDiffAt_witness_step_unary {f z fp : BHist} :
    CplxDiffAt f z fp ->
      ∃ h : BHist, ∃ q : BHist, UnaryHistory h ∧ UnaryHistory q ∧ Cont f h q ∧ hsame q fp := by
  intro derivative
  cases derivative with
  | intro _functionCarrier derivativeRest =>
      cases derivativeRest with
      | intro _pointCarrier derivativeRest =>
          cases derivativeRest with
          | intro _derivativeCarrier derivativeRest =>
              cases derivativeRest with
              | intro witness classifier =>
                  cases witness with
                  | intro h witnessRest =>
                      cases witnessRest with
                      | intro q quotient =>
                          have stepUnary := CplxDiffQuot_step_unary quotient
                          exact Exists.intro h
                            (Exists.intro q
                              (And.intro stepUnary.left
                                (And.intro stepUnary.right.left
                                  (And.intro stepUnary.right.right (classifier quotient)))))

end BEDC.Derived.DerivativeUp
