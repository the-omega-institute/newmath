import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyTailDiagonalUp : Type where
  | mk
      (tailSchedule streamWindows dyadicTolerances regSeqRatReadback realSeal
        transport replay provenance localNameCert : BHist) :
      RegularCauchyTailDiagonalUp
  deriving DecidableEq

end BEDC.Derived
