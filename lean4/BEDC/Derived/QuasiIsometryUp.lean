import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive QuasiIsometryUp : Type where
  | mk
      (sourceMetric targetMetric coarseGraph distortion coarseSurjectivity distanceReadback
        completionFacing transport replay provenance name : BHist) :
      QuasiIsometryUp
  deriving DecidableEq

end BEDC.Derived
