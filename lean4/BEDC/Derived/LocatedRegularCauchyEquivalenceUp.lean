import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedRegularCauchyEquivalenceUp : Type where
  | mk
      (leftName rightName leftWindow rightWindow tolerance comparison verdict
        transport replay provenance localName : BHist)

end BEDC.Derived
