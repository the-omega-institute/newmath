import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem LinearMapSingletonClassifier_eval_context_pair_iff {p q f x g y : BHist} :
    LinearMapSingletonClassifier (append p (LinearMapSingletonEval f x))
        (append q (LinearMapSingletonEval g y)) ↔
      LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q := by
  constructor
  · intro classified
    have split :=
      (LinearMapSingletonClassifier_append_pair_carrier_iff
        (p := p) (q := LinearMapSingletonEval f x)
        (r := q) (s := LinearMapSingletonEval g y)).mp classified
    exact And.intro split.left split.right.right.left
  · intro carriers
    have leftEval : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
      hsame_refl BHist.Empty
    have rightEval : LinearMapSingletonCarrier (LinearMapSingletonEval g y) :=
      hsame_refl BHist.Empty
    exact
      (LinearMapSingletonClassifier_append_pair_carrier_iff
        (p := p) (q := LinearMapSingletonEval f x)
        (r := q) (s := LinearMapSingletonEval g y)).mpr
        (And.intro carriers.left
          (And.intro leftEval (And.intro carriers.right rightEval)))

end BEDC.Derived.LinearMapUp
