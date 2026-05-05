import BEDC.Derived.LinearMapUp
import BEDC.Derived.LinearMapUp.CompContinuation

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

theorem LinearMapSingletonEval_context_comp_continuation_pair_classifier
    {p g f x y r s : BHist} :
    LinearMapSingletonCarrier p -> LinearMapSingletonCarrier y ->
      Cont (append p (LinearMapSingletonEval f x)) y r ->
        Cont (LinearMapSingletonEval (LinearMapSingletonComp g f) x) BHist.Empty s ->
          LinearMapSingletonClassifier r s := by
  intro carrierP carrierY evalCont compCont
  have evalCarrier : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
    hsame_refl BHist.Empty
  have contextCarrier : LinearMapSingletonCarrier (append p (LinearMapSingletonEval f x)) :=
    append_eq_empty_iff.mpr (And.intro carrierP evalCarrier)
  have resultR : LinearMapSingletonCarrier r :=
    cont_respects_hsame contextCarrier carrierY evalCont (cont_right_unit BHist.Empty)
  have resultS : LinearMapSingletonCarrier s :=
    cont_respects_hsame (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) compCont
      (cont_right_unit BHist.Empty)
  exact And.intro resultR (And.intro resultS (hsame_trans resultR (hsame_symm resultS)))

end BEDC.Derived.LinearMapUp
