import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafConsumerAccessTrace_append_no_zero_extension
    {root row tail : BHist} {left right : List BHist} :
    SheafConsumerAccessTrace root left -> SheafConsumerAccessTrace root right ->
      List.Mem row (left ++ right) -> hsame row (BHist.e0 tail) -> False := by
  intro leftTrace rightTrace rowMem sameRow
  have appended :
      UnaryHistory root ∧ SheafConsumerAccessTrace root (left ++ right) :=
    SheafConsumerAccessTrace_append_closed leftTrace rightTrace
  have rowUnary : UnaryHistory row :=
    appended.right.right row rowMem
  exact unary_no_zero_extension (unary_transport rowUnary sameRow)

end BEDC.Derived.SheafUp
