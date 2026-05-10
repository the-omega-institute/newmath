import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem LinearMapSingletonComp_continuation_pair_classifier {g f y z r s : BHist} :
    Cont (LinearMapSingletonComp g f) y r ->
      Cont (LinearMapSingletonComp g f) z s ->
        LinearMapSingletonCarrier y ->
          LinearMapSingletonCarrier z -> LinearMapSingletonClassifier r s := by
  intro leftCont rightCont carrierY carrierZ
  have resultR : LinearMapSingletonCarrier r :=
    cont_respects_hsame (hsame_refl BHist.Empty) carrierY leftCont
      (cont_right_unit BHist.Empty)
  have resultS : LinearMapSingletonCarrier s :=
    cont_respects_hsame (hsame_refl BHist.Empty) carrierZ rightCont
      (cont_right_unit BHist.Empty)
  exact And.intro resultR (And.intro resultS (hsame_trans resultR (hsame_symm resultS)))

theorem LinearMapSingletonComp_identity_unit_laws {f left right x : BHist} :
    LinearMapSingletonCarrier f -> Cont BHist.Empty f left -> Cont f BHist.Empty right ->
      LinearMapSingletonClassifier left f ∧ LinearMapSingletonClassifier right f ∧
        LinearMapSingletonClassifier (LinearMapSingletonComp BHist.Empty f) f ∧
          LinearMapSingletonClassifier (LinearMapSingletonComp f BHist.Empty) f ∧
            LinearMapSingletonClassifier (LinearMapSingletonEval left x)
              (LinearMapSingletonEval f x) ∧
              LinearMapSingletonClassifier (LinearMapSingletonEval right x)
                (LinearMapSingletonEval f x) := by
  intro carrierF leftRel rightRel
  have leftSame : hsame left f := cont_left_unit_result leftRel
  have rightSame : hsame right f := cont_deterministic rightRel (cont_right_unit f)
  have leftCarrier : LinearMapSingletonCarrier left := hsame_trans leftSame carrierF
  have rightCarrier : LinearMapSingletonCarrier right := hsame_trans rightSame carrierF
  have evalClassified :
      LinearMapSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  exact
    And.intro
      (And.intro leftCarrier (And.intro carrierF leftSame))
      (And.intro
        (And.intro rightCarrier (And.intro carrierF rightSame))
        (And.intro
          (And.intro (hsame_refl BHist.Empty) (And.intro carrierF (hsame_symm carrierF)))
          (And.intro
            (And.intro (hsame_refl BHist.Empty)
              (And.intro carrierF (hsame_symm carrierF)))
            (And.intro evalClassified evalClassified))))

end BEDC.Derived.LinearMapUp
