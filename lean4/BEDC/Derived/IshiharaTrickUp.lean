import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive IshiharaTrickUp : Type where
  | mk :
      (schedule readback tolerance realSeal branchRow transport replay provenance localName : BHist) →
        IshiharaTrickUp
  deriving DecidableEq

end BEDC.Derived
