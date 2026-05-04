import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.DenominatorContext

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealConstantHistoryCarrier_cont_unary_denominator_context_closed
    {d pref tail mid out : BHist} :
    RealConstantHistoryCarrier (BHist.e1 d) -> UnaryHistory pref -> UnaryHistory tail ->
      Cont pref d mid -> Cont mid tail out -> RealConstantHistoryCarrier (BHist.e1 out) := by
  intro carrier prefUnary tailUnary prefCont outCont
  have ratCarrier : RatHistoryCarrier d :=
    RealConstantHistoryCarrier_e1_iff_rat.mp carrier
  have contextCarrier :
      RatHistoryCarrier (append pref (append d tail)) :=
    RatHistoryCarrier_unary_denominator_context_closed prefUnary ratCarrier tailUnary
  have sameOut : hsame (append pref (append d tail)) out := by
    have outEq : out = append (append pref d) tail :=
      Eq.trans outCont (congrArg (fun h : BHist => append h tail) prefCont)
    exact hsame_trans (hsame_symm (append_assoc pref d tail)) outEq.symm
  exact RealConstantHistoryCarrier_e1_iff_rat.mpr
    (RatHistoryCarrier_hsame_transport sameOut contextCarrier)

end BEDC.Derived.RealUp
