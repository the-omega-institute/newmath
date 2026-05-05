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

end BEDC.Derived.LinearMapUp
