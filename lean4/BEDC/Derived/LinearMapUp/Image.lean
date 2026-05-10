import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def LinearMapSingletonImage (f y : BHist) : Prop :=
  exists x : BHist,
    LinearMapSingletonCarrier x ∧
      LinearMapSingletonClassifier (LinearMapSingletonEval f x) y

theorem LinearMapSingletonImage_submodule_closure {f y z r : BHist} :
    LinearMapSingletonCarrier f ->
      LinearMapSingletonImage f y ->
        LinearMapSingletonClassifier y z ->
          LinearMapSingletonImage f z ∧ LinearMapSingletonImage f BHist.Empty ∧
            LinearMapSingletonImage f (append y z) ∧
              LinearMapSingletonImage f (LinearMapSingletonEval r y) := by
  intro _carrierF imageY classifiedYZ
  cases imageY with
  | intro x witness =>
      have carrierX : LinearMapSingletonCarrier x := witness.left
      have evalCarrier : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
        hsame_refl BHist.Empty
      have emptyCarrier : LinearMapSingletonCarrier BHist.Empty :=
        hsame_refl BHist.Empty
      have carrierY : LinearMapSingletonCarrier y := witness.right.right.left
      have carrierZ : LinearMapSingletonCarrier z := classifiedYZ.right.left
      have evalToZ : LinearMapSingletonClassifier (LinearMapSingletonEval f x) z :=
        And.intro evalCarrier
          (And.intro carrierZ
            (hsame_trans witness.right.right.right classifiedYZ.right.right))
      have evalToEmpty : LinearMapSingletonClassifier (LinearMapSingletonEval f x) BHist.Empty :=
        And.intro evalCarrier (And.intro emptyCarrier evalCarrier)
      have appendCarrier : LinearMapSingletonCarrier (append y z) :=
        append_eq_empty_iff.mpr (And.intro carrierY carrierZ)
      have evalToAppend : LinearMapSingletonClassifier (LinearMapSingletonEval f x) (append y z) :=
        And.intro evalCarrier
          (And.intro appendCarrier (hsame_trans evalCarrier (hsame_symm appendCarrier)))
      have scalarEvalCarrier :
          LinearMapSingletonCarrier (LinearMapSingletonEval r y) :=
        hsame_refl BHist.Empty
      have evalToScalar : LinearMapSingletonClassifier
          (LinearMapSingletonEval f x) (LinearMapSingletonEval r y) :=
        And.intro evalCarrier
          (And.intro scalarEvalCarrier
            (hsame_trans evalCarrier (hsame_symm scalarEvalCarrier)))
      exact And.intro
        (Exists.intro x (And.intro carrierX evalToZ))
        (And.intro
          (Exists.intro x (And.intro carrierX evalToEmpty))
          (And.intro
            (Exists.intro x (And.intro carrierX evalToAppend))
            (Exists.intro x (And.intro carrierX evalToScalar))))

end BEDC.Derived.LinearMapUp
