import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryCarrier_visible_payload_determinism {Left Right : BHist → Prop}
    {h l l' r r' : BHist} :
    (hsame h (BHist.e0 l) → Left l → hsame h (BHist.e0 l') → Left l' → hsame l l') ∧
      (hsame h (BHist.e1 r) → Right r → hsame h (BHist.e1 r') → Right r' →
        hsame r r') := by
  constructor
  · intro sameLeft _ sameLeft' _
    exact hsame_e0_iff.mp (hsame_trans (hsame_symm sameLeft) sameLeft')
  · intro sameRight _ sameRight' _
    exact hsame_e1_iff.mp (hsame_trans (hsame_symm sameRight) sameRight')

end BEDC.Derived.SumUp
