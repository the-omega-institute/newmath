import BEDC.Derived.ComplexDiffUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ComplexDiffUp

theorem CplxDiffAt_witness_step_nonzero {f z fp : BHist} :
    CplxDiffAt f z fp ->
      exists h : BHist, exists q : BHist,
        CplxNonZero h ∧ CplxDiffQuot f z h q ∧ Cont f h q ∧ hsame q fp := by
  intro diff
  cases diff with
  | intro _functionCarrier diffRest =>
      cases diffRest with
      | intro _pointCarrier diffRest =>
          cases diffRest with
          | intro _derivativeCarrier diffRest =>
              cases diffRest with
              | intro witness classifier =>
                  cases witness with
                  | intro h witnessRest =>
                      cases witnessRest with
                      | intro q quotient =>
                          cases quotient with
                          | intro functionCarrier quotientRest =>
                              cases quotientRest with
                              | intro pointCarrier quotientRest =>
                                  cases quotientRest with
                                  | intro stepNonzero quotientRest =>
                                      cases quotientRest with
                                      | intro quotientCarrier ledger =>
                                          have rebuilt : CplxDiffQuot f z h q :=
                                            And.intro functionCarrier
                                              (And.intro pointCarrier
                                                (And.intro stepNonzero
                                                  (And.intro quotientCarrier ledger)))
                                          exact Exists.intro h
                                            (Exists.intro q
                                              (And.intro stepNonzero
                                                (And.intro rebuilt
                                                  (And.intro ledger (classifier rebuilt)))))

end BEDC.Derived.ComplexDifferentiabilityUp
