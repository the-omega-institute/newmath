import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafConsumerTraceCompositionSource
    (root : BHist) (left right composed : List BHist) : Prop :=
  UnaryHistory root ∧ Cont BHist.Empty root root ∧
    SheafConsumerAccessTrace root left ∧ SheafConsumerAccessTrace root right ∧
      composed = left ++ right ∧ SheafConsumerAccessTrace root composed

end BEDC.Derived.SheafUp
