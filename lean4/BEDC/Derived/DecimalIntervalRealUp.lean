import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DecimalIntervalRealUp : Type where
  | mk
      (lower upper tolerance windows bracket readback realSeal locatedRow transport replay provenance
        name : BHist) : DecimalIntervalRealUp

end BEDC.Derived
