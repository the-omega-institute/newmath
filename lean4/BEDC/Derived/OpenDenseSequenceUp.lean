import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive OpenDenseSequenceUp : Type where
  | mk
      (source schedule denseLedger window readback transport replay provenance name : BHist) :
      OpenDenseSequenceUp
  deriving DecidableEq

end BEDC.Derived
