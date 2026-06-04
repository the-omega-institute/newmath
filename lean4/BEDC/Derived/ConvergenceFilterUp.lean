import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ConvergenceFilterUp : Type where
  | mk
      (filterBase neighbourhood limitPoint window readback realSeal transport replay provenance name :
        BHist) :
      ConvergenceFilterUp
  deriving DecidableEq

end BEDC.Derived
