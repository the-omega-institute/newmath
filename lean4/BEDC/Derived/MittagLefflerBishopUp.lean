import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MittagLefflerBishopUp : Type where
  | mk
      (interval window mesh stream readback realSeal transport replay provenance name : BHist) :
      MittagLefflerBishopUp
  deriving DecidableEq

end BEDC.Derived
