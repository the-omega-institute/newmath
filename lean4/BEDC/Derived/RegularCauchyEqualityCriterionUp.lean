import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyEqualityCriterionUp : Type where
  | mk
      (leftWindow rightWindow leftReadback rightReadback dyadicTail commonTail
        equalityBoundary transport replay provenance localName : BHist) :
      RegularCauchyEqualityCriterionUp
  deriving DecidableEq

end BEDC.Derived
