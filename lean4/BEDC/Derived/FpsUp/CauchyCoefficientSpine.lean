import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def FpsCauchyCoefficientSpine (F G : BHist -> BHist) (n : BHist) : BHist :=
  append (F n) (G n)

end BEDC.Derived.FpsUp
