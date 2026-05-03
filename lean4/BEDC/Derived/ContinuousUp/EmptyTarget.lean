import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_empty_target_iff {source modulus : BHist} :
    ContinuousModulusWitness source modulus BHist.Empty ↔
      hsame source BHist.Empty ∧ hsame modulus BHist.Empty := by
  constructor
  · intro witness
    have split := cont_empty_result_inversion witness.right.right.right
    exact And.intro split.left split.right
  · intro endpoints
    cases endpoints.left
    cases endpoints.right
    exact And.intro unary_empty
      (And.intro unary_empty (And.intro unary_empty (cont_intro rfl)))

theorem ContinuousModulusChain_empty_target_iff {source first second : BHist} :
    ContinuousModulusChain source first second BHist.Empty ↔
      hsame source BHist.Empty ∧ hsame first BHist.Empty ∧ hsame second BHist.Empty := by
  constructor
  · intro chain
    cases chain with
    | intro _sourceCarrier rest =>
        cases rest with
        | intro _firstCarrier rest =>
            cases rest with
            | intro _secondCarrier rest =>
                cases rest with
                | intro _targetCarrier chainWitness =>
                    cases chainWitness with
                    | intro middle middleData =>
                        cases middleData with
                        | intro firstRel secondRel =>
                            have rightParts := cont_empty_result_inversion secondRel
                            have leftParts : source = BHist.Empty ∧ first = BHist.Empty := by
                              cases rightParts.left
                              exact cont_empty_result_inversion firstRel
                            exact And.intro leftParts.left
                              (And.intro leftParts.right rightParts.right)
  · intro endpoints
    cases endpoints.left
    cases endpoints.right.left
    cases endpoints.right.right
    exact And.intro unary_empty
      (And.intro unary_empty
        (And.intro unary_empty
          (And.intro unary_empty
            (Exists.intro BHist.Empty
              (And.intro (cont_right_unit BHist.Empty) (cont_right_unit BHist.Empty))))))

end BEDC.Derived.ContinuousUp
