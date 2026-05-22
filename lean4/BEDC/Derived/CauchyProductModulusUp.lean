import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyProductModulusUp : Type where
  | mk
      (sourceA sourceB windowA windowB dyadicA dyadicB budget modulus readback sealRow
        transport routes provenance name : BHist) :
      CauchyProductModulusUp
  deriving DecidableEq

end BEDC.Derived
