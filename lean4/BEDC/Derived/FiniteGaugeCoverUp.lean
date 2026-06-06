import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteGaugeCoverUp : Type where
  | mk
      (gauge cells tags mesh dyadicReadback realSeal cousinHandoff riemannHandoff
        gaugeIntegralHandoff transport provenance name : BHist) :
      FiniteGaugeCoverUp

end BEDC.Derived
