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

theorem ContinuousModulusWitness_right_e1_result_exactness {source modulus target : BHist} :
    ContinuousModulusWitness source (BHist.e1 modulus) (BHist.e1 target) ->
      ContinuousModulusWitness source modulus target := by
  intro witness
  cases witness with
  | intro sourceCarrier rest =>
      cases rest with
      | intro modulusCarrier rest =>
          cases rest with
          | intro targetCarrier modulusRel =>
              exact
                And.intro sourceCarrier
                  (And.intro (unary_e1_inversion modulusCarrier)
                    (And.intro (unary_e1_inversion targetCarrier)
                      (cont_step_rules_inversion_pair.right modulusRel)))

theorem ContinuousModulusWitness_right_e1_visible_source_exactness
    {source modulus target sourceTail : BHist} :
    ContinuousModulusWitness source (BHist.e1 modulus) (BHist.e1 target) ->
      hsame source (BHist.e1 sourceTail) ->
        ContinuousModulusWitness (BHist.e1 sourceTail) modulus target := by
  intro witness sameSource
  have tailWitness : ContinuousModulusWitness source modulus target :=
    ContinuousModulusWitness_right_e1_result_exactness witness
  cases sameSource
  exact tailWitness

end BEDC.Derived.ContinuousUp
