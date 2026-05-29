import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetricReverseTriangleInequalityUp : Type where
  | mk (M DXZ DYZ G E W R S H C P N : BHist) : MetricReverseTriangleInequalityUp
  deriving DecidableEq

end BEDC.Derived
