import BEDC.Derived.IntUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

def PositiveUnaryDenominator (den : BHist) : Prop :=
  ∃ tail : BHist, hsame den (BHist.e1 tail) ∧ UnaryHistory tail

def RatSourceSpec (normalized : BMark → BHist → BHist → Prop) (sign : BMark)
    (num den : BHist) : Prop :=
  BEDC.Derived.IntUp.IntCarrier sign num ∧ PositiveUnaryDenominator den ∧
    normalized sign num den

end BEDC.Derived.RatUp
