import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ComplexPointwiseDifference (s t : BHist -> BHist) (n : BHist) : BHist :=
  append (s n) (t n)

end BEDC.Derived.ComplexLimitUp
