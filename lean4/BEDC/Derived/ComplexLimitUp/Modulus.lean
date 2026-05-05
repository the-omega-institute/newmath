import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def CplxMod (z M : BHist) : Prop :=
  ComplexHistoryCarrier z ∧ UnaryHistory M ∧
    (ComplexDistance z BHist.Empty M ∨ ComplexDistance BHist.Empty z M)

end BEDC.Derived.ComplexLimitUp
