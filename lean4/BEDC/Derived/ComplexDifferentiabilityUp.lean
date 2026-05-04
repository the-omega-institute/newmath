import BEDC.Derived.ComplexDiffUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
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

theorem CplxDiffAt_witness_nonzero_unary_step {f z fp : BHist} :
    CplxDiffAt f z fp -> ∃ h : BHist, ∃ q : BHist,
      CplxNonZero h ∧ UnaryHistory h ∧ UnaryHistory q ∧ CplxDiffQuot f z h q ∧
        Cont f h q ∧ hsame q fp := by
  intro diff
  cases CplxDiffAt_witness_step_nonzero diff with
  | intro h witness =>
      cases witness with
      | intro q data =>
          cases data with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotient rest =>
                  cases rest with
                  | intro ledger quotientClass =>
                      have unaryReadback := CplxDiffQuot_step_unary quotient
                      exact Exists.intro h
                        (Exists.intro q
                          (And.intro stepNonzero
                            (And.intro unaryReadback.left
                              (And.intro unaryReadback.right.left
                                (And.intro quotient
                                  (And.intro ledger quotientClass))))))

end BEDC.Derived.ComplexDifferentiabilityUp
