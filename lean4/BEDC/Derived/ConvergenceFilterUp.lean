import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ConvergenceFilterUp : Type where
  | mk
      (filterBase neighbourhood limitPoint window readback realSeal transport replay provenance name :
        BHist) :
      ConvergenceFilterUp
  deriving DecidableEq

def convergenceFilterRows : ConvergenceFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist
  | ConvergenceFilterUp.mk F Nb x W R E H C P N => [F, Nb, x, W, R, E, H, C, P, N]

end BEDC.Derived
