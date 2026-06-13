import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedCauchyLimitUp : Type where
  | mk
      (stream readback tolerance tail candidate uniqueness realSeal transport replay provenance name :
        BHist) :
      LocatedCauchyLimitUp

end BEDC.Derived
