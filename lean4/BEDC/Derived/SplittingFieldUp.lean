import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.SplittingFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def SplittingFieldRootCarrierPacket
    (E P R F C H Pi : BHist) : Prop :=
  Cont E P C ∧
    hsame (append R F) H ∧
      hsame (append C H) Pi

theorem SplittingFieldRootCarrierPacket_factor_rows_unique {E P R F F' C H Pi : BHist} :
    SplittingFieldRootCarrierPacket E P R F C H Pi ->
      SplittingFieldRootCarrierPacket E P R F' C H Pi ->
        hsame (append R F) (append R F') ∧ hsame F F' := by
  intro left right
  have sameFactorRows : hsame (append R F) (append R F') :=
    hsame_trans left.right.left (hsame_symm right.right.left)
  exact And.intro sameFactorRows (append_left_cancel (h := R) sameFactorRows)

end BEDC.Derived.SplittingFieldUp
