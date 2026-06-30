import BEDC.Derived.RHRoute.CausalReflectionPositiveCone
import BEDC.Derived.RHRoute.PrimeCausalTower
import BEDC.Derived.RHRoute.ThreeAxisOrbitCollapse
import BEDC.Foundations.TriAxisCoverage

namespace BEDC.Derived.RHRoute.TriAxisCoverage

open BEDC.Foundations.TriangleGenerationSystem
open BEDC.Foundations.TriAxisCoverage

def rhRouteAxisObjCode : TriAxisObjCode :=
  TriAxisObjCode.pairGen
    (TriAxisObjCode.distinctionGen TriAxisObjCode.base)
    (TriAxisObjCode.pairGen
      (TriAxisObjCode.timeGen TriAxisObjCode.base)
      (TriAxisObjCode.symmetryGen TriAxisObjCode.base))

theorem rhRouteAxisObjCode_covers_distinction :
    CoversDistinction rhRouteAxisObjCode := by
  unfold rhRouteAxisObjCode
  exact CoversDistinction.pairLeft
    (CoversDistinction.here TriAxisObjCode.base)

theorem rhRouteAxisObjCode_covers_time :
    CoversTime rhRouteAxisObjCode := by
  unfold rhRouteAxisObjCode
  exact CoversTime.pairRight
    (CoversTime.pairLeft
      (CoversTime.here TriAxisObjCode.base))

theorem rhRouteAxisObjCode_covers_symmetry :
    CoversSymmetry rhRouteAxisObjCode := by
  unfold rhRouteAxisObjCode
  exact CoversSymmetry.pairRight
    (CoversSymmetry.pairRight
      (CoversSymmetry.here TriAxisObjCode.base))

def rhRouteAxisObjCode_covers_all :
    AxisDemand.Covers AxisDemand.allThree rhRouteAxisObjCode :=
  ⟨rhRouteAxisObjCode_covers_distinction,
    rhRouteAxisObjCode_covers_time,
    rhRouteAxisObjCode_covers_symmetry⟩

def causalReflectionPositiveConeTriAxisObligation :
    TriAxisBindingObligation
      BEDC.Derived.RHRoute.CausalReflectionPositiveCone.CausalReflectionPositiveCone
    where
  proposed_code := rhRouteAxisObjCode
  projection_forced := triAxisProjection_forced_unique rhRouteAxisObjCode
  demanded_axes := AxisDemand.allThree
  covers_some := rhRouteAxisObjCode_covers_all

def primeCausalTowerTriAxisObligation :
    TriAxisBindingObligation
      BEDC.Derived.RHRoute.PrimeCausalTower.PrimeCausalTower
    where
  proposed_code := rhRouteAxisObjCode
  projection_forced := triAxisProjection_forced_unique rhRouteAxisObjCode
  demanded_axes := AxisDemand.allThree
  covers_some := rhRouteAxisObjCode_covers_all

def threeAxisOrbitCollapseKernelTriAxisObligation :
    TriAxisBindingObligation
      BEDC.Derived.RHRoute.ThreeAxisOrbitCollapse.ThreeAxisOrbitCollapseKernel
    where
  proposed_code := rhRouteAxisObjCode
  projection_forced := triAxisProjection_forced_unique rhRouteAxisObjCode
  demanded_axes := AxisDemand.allThree
  covers_some := rhRouteAxisObjCode_covers_all

end BEDC.Derived.RHRoute.TriAxisCoverage
