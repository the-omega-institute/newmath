import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HeatKernelUp : Type where
  | mk
      (kernelWindow stencilSource semigroup readback realSeal transport continuation provenance
        name : BHist) :
      HeatKernelUp
  deriving DecidableEq

end BEDC.Derived
