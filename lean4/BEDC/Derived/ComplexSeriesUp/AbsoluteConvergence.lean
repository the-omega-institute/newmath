import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexLimitUp

def ComplexAbsConv (zero : BHist) (modulus : BHist -> BHist) (bound : BHist) : Prop :=
  exists absps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
    (forall n : BHist, UnaryHistory n -> ComplexAbsPartSum zero modulus n (absps n)) /\
      ComplexLimit absps N bound M

end BEDC.Derived.ComplexSeriesUp
