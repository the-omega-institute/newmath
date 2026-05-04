import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RatDenomUnitClassifier_cont_context_e1_pair_readback
    {d e prefD prefE tailD tailE midD midE outD outE leftTail rightTail : BHist} :
    RatDenomUnitClassifier d e -> RatDenomUnitClassifier prefD prefE ->
      RatDenomUnitClassifier tailD tailE -> Cont prefD d midD -> Cont midD tailD outD ->
        Cont prefE e midE -> Cont midE tailE outE -> hsame outD (BHist.e1 leftTail) ->
          hsame outE (BHist.e1 rightTail) ->
            UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
  intro classified classifiedPref classifiedTail prefDCont outDCont prefECont outECont sameOutD
    sameOutE
  have midClassified : RatDenomUnitClassifier midD midE :=
    RatDenomUnitClassifier_continuation_closed classifiedPref classified prefDCont prefECont
  have outClassified : RatDenomUnitClassifier outD outE :=
    RatDenomUnitClassifier_continuation_closed midClassified classifiedTail outDCont outECont
  have displayed : RatDenomUnitClassifier (BHist.e1 leftTail) (BHist.e1 rightTail) := by
    constructor
    · exact RatDenomUnitCarrier_hsame_transport sameOutD outClassified.left
    · constructor
      · exact RatDenomUnitCarrier_hsame_transport sameOutE outClassified.right.left
      · exact hsame_trans (hsame_symm sameOutD)
          (hsame_trans outClassified.right.right sameOutE)
  exact RatDenomUnitClassifier_e1_tail_iff.mp displayed

end BEDC.Derived.FieldUp
