import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_left_e1_result_cases {source modulus target : BHist} :
    ContinuousModulusWitness (BHist.e1 source) modulus (BHist.e1 target) →
      (modulus = BHist.Empty ∧ UnaryHistory source ∧ hsame source target) ∨
        (∃ modulusTail : BHist,
          modulus = BHist.e1 modulusTail ∧
            ContinuousModulusWitness (BHist.e1 source) modulusTail target) := by
  intro witness
  cases witness with
  | intro sourceCarrier rest =>
      cases rest with
      | intro modulusCarrier rest =>
          cases rest with
          | intro targetCarrier modulusRel =>
              have resultCases := cont_e1_result_inversion modulusRel
              cases resultCases with
              | inl emptyCase =>
                  cases emptyCase with
                  | intro modulusEmpty sameTarget =>
                      cases modulusEmpty
                      exact
                        Or.inl
                          (And.intro rfl
                            (And.intro sourceCarrier (hsame_e1_iff.mp sameTarget)))
              | inr tailCase =>
                  cases tailCase with
                  | intro modulusTail tailData =>
                      cases tailData with
                      | intro modulusEq tailRel =>
                          cases modulusEq
                          exact
                            Or.inr
                              (Exists.intro modulusTail
                                (And.intro rfl
                                  (And.intro sourceCarrier
                                    (And.intro modulusCarrier
                                      (And.intro targetCarrier tailRel)))))

end BEDC.Derived.ContinuousUp
