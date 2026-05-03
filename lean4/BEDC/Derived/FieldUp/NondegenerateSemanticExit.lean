import BEDC.Derived.FieldUp.SingletonAppend
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem ratup_fieldup_empty_context_nondegenerate_witness {L R : BHist} :
    fieldSingletonEmptyCarrier L ->
      fieldSingletonEmptyCarrier R ->
        RatHistoryCarrier (append L (append (BHist.e1 BHist.Empty) R)) ∧
          (fieldSingletonEmptyCarrier (append L (append (BHist.e1 BHist.Empty) R)) ->
            False) ∧
          fieldSingletonEmptyNonZero (append L (append (BHist.e1 BHist.Empty) R)) := by
  intro carrierL carrierR
  let witness := append L (append (BHist.e1 BHist.Empty) R)
  have coreCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have sameInner : hsame (append (BHist.e1 BHist.Empty) R) (BHist.e1 BHist.Empty) := by
    cases carrierR
    exact append_empty_right (BHist.e1 BHist.Empty)
  have sameWitness : hsame witness (BHist.e1 BHist.Empty) := by
    cases carrierL
    exact hsame_trans (append_empty_left (append (BHist.e1 BHist.Empty) R)) sameInner
  have witnessCarrier : RatHistoryCarrier witness :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameWitness) coreCarrier
  have witnessReject : fieldSingletonEmptyCarrier witness -> False :=
    fun singleton => RatHistoryCarrier_not_empty witnessCarrier singleton
  exact ⟨witnessCarrier, witnessReject, fun classified => witnessReject classified.left⟩

end BEDC.Derived.FieldUp
