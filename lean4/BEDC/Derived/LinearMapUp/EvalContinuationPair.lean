import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem LinearMapSingletonEval_comp_continuation_pair_classifier {g f x r s : BHist} :
    LinearMapSingletonCarrier g ->
      Cont (LinearMapSingletonEval f x) g r ->
        Cont (LinearMapSingletonEval (LinearMapSingletonComp g f) x) BHist.Empty s ->
          LinearMapSingletonClassifier r s := by
  intro carrierG evalCont compCont
  have resultR : LinearMapSingletonCarrier r :=
    cont_respects_hsame (hsame_refl BHist.Empty) carrierG evalCont (cont_right_unit BHist.Empty)
  have resultS : LinearMapSingletonCarrier s :=
    cont_respects_hsame (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) compCont
      (cont_right_unit BHist.Empty)
  exact And.intro resultR (And.intro resultS (hsame_trans resultR (hsame_symm resultS)))

end BEDC.Derived.LinearMapUp
