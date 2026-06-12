import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteFanCompactnessUp : Type where
  | mk
      (fan cover modulus compact metric continuous uniform rat minimum provenance name : BHist) :
      FiniteFanCompactnessUp
  deriving DecidableEq

end BEDC.Derived
