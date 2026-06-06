import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RealCauchyFilterMonadUnitUp : Type where
  | packet
      (real filterBase cauchyFilter completion universalProperty regSeq stream transport replay
        provenance name : BHist) :
      RealCauchyFilterMonadUnitUp
  deriving DecidableEq

end BEDC.Derived
