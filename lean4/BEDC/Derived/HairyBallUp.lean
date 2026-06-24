import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HairyBallUp : Type where
  | mk (sphere tangent field zero obstruction realSeal transport replay provenance name : BHist) :
      HairyBallUp
  deriving DecidableEq

end BEDC.Derived
