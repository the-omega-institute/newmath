import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive RegularCauchyTailProductBoundUp : Type where
  | mk
      (tailWindow productBudget regularProduct sourceLeft sourceRight realSeal
        transport replay provenance name :
          _root_.BEDC.FKernel.Hist.BHist) :
      RegularCauchyTailProductBoundUp

end BEDC.Derived
