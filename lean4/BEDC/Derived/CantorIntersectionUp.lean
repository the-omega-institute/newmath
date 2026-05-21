import BEDC.FKernel.Hist

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Hist

inductive CantorIntersectionCarrier where
  | packet
      (nestedIntersection widthWindow diagonalSelector endpointEnclosure regSeqRatHandoff
        realSeal transport package nameCert : BHist) :
      CantorIntersectionCarrier

structure CantorIntersectionCarrier_namecert_obligations where
  carrier : CantorIntersectionCarrier -> Prop
  finiteWindowClassifier : CantorIntersectionCarrier -> CantorIntersectionCarrier -> Prop
  selectorStability : CantorIntersectionCarrier -> CantorIntersectionCarrier -> Prop
  regSeqRatHandoffExactness : CantorIntersectionCarrier -> Prop
  realSealNonescape : CantorIntersectionCarrier -> Prop

end BEDC.Derived.CantorIntersectionUp
