import BEDC.Derived.RHRoute.PrimePhaseRadialReadback

namespace BEDC.Derived.RHRoute.InfinitePrimeTorusCompatibility

open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RationalUp

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev IsPrime := BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime
abbrev RatComplex := BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

def WindowInclusion (small large : PrimeWindow) : Prop :=
  (p : Nat) -> small.mem p -> large.mem p

def WindowInclusion.refl (W : PrimeWindow) : WindowInclusion W W :=
  fun _p member => member

def WindowInclusion.trans {small middle large : PrimeWindow}
    (left : WindowInclusion small middle)
    (right : WindowInclusion middle large) :
    WindowInclusion small large :=
  fun p member => right p (left p member)

-- 有限素数环面只暴露有限窗口坐标, 每个坐标带单位相位读回。
structure FinitePrimeTorusPoint (window : PrimeWindow) where
  phase : (p : Nat) -> window.mem p -> RatComplex
  unit_phase :
    (p : Nat) -> (member : window.mem p) ->
      RatEq (ratComplexNormSq (phase p member)) ratOne

structure FinitePrimeSubtorus where
  window : PrimeWindow
  point : FinitePrimeTorusPoint window

def projectFinitePrimeTorusPoint {small large : PrimeWindow}
    (incl : WindowInclusion small large)
    (point : FinitePrimeTorusPoint large) :
    FinitePrimeTorusPoint small where
  phase := fun p member => point.phase p (incl p member)
  unit_phase := fun p member => point.unit_phase p (incl p member)

structure FiniteProjectionCompatible {small large : PrimeWindow}
    (incl : WindowInclusion small large)
    (smallPoint : FinitePrimeTorusPoint small)
    (largePoint : FinitePrimeTorusPoint large) where
  projected_eq :
    (p : Nat) -> (member : small.mem p) ->
      smallPoint.phase p member = largePoint.phase p (incl p member)

theorem finite_projection_coordinate_exact {small large : PrimeWindow}
    (incl : WindowInclusion small large)
    (point : FinitePrimeTorusPoint large)
    (p : Nat) (member : small.mem p) :
    (projectFinitePrimeTorusPoint incl point).phase p member =
      point.phase p (incl p member) := by
  rfl

theorem finite_projection_unit_phase {small large : PrimeWindow}
    (incl : WindowInclusion small large)
    (point : FinitePrimeTorusPoint large)
    (p : Nat) (member : small.mem p) :
    RatEq
      (ratComplexNormSq
        ((projectFinitePrimeTorusPoint incl point).phase p member))
      ratOne := by
  exact point.unit_phase p (incl p member)

theorem finite_projection_is_compatible {small large : PrimeWindow}
    (incl : WindowInclusion small large)
    (point : FinitePrimeTorusPoint large) :
    FiniteProjectionCompatible incl
      (projectFinitePrimeTorusPoint incl point) point := by
  constructor
  intro p member
  rfl

theorem finite_projection_composes_coordinate
    {small middle large : PrimeWindow}
    (left : WindowInclusion small middle)
    (right : WindowInclusion middle large)
    (point : FinitePrimeTorusPoint large)
    (p : Nat) (member : small.mem p) :
    (projectFinitePrimeTorusPoint left
        (projectFinitePrimeTorusPoint right point)).phase p member =
      (projectFinitePrimeTorusPoint
        (WindowInclusion.trans left right) point).phase p member := by
  rfl

theorem finite_projection_identity_coordinate
    (window : PrimeWindow)
    (point : FinitePrimeTorusPoint window)
    (p : Nat) (member : window.mem p) :
    (projectFinitePrimeTorusPoint
      (WindowInclusion.refl window) point).phase p member =
      point.phase p member := by
  rfl

theorem finite_subtorus_coordinate_prime
    (subtorus : FinitePrimeSubtorus)
    {p : Nat} :
    subtorus.window.mem p -> IsPrime p := by
  intro member
  exact All.mem subtorus.window.all_prime member

def leftIntersectionProjection {left right : PrimeWindow}
    (point : FinitePrimeTorusPoint left) :
  FinitePrimeTorusPoint (PrimeWindow.inter left right) :=
  projectFinitePrimeTorusPoint
    (fun _p member => PrimeWindow.mem_inter_left member) point

def rightIntersectionProjection {left right : PrimeWindow}
    (point : FinitePrimeTorusPoint right) :
  FinitePrimeTorusPoint (PrimeWindow.inter left right) :=
  projectFinitePrimeTorusPoint
    (fun _p member => PrimeWindow.mem_inter_right member) point

structure FiniteSubtorusOverlapCompatible
    {left right : PrimeWindow}
    (leftPoint : FinitePrimeTorusPoint left)
    (rightPoint : FinitePrimeTorusPoint right) where
  overlap_eq :
    (p : Nat) -> (member : (PrimeWindow.inter left right).mem p) ->
      (leftIntersectionProjection leftPoint).phase p member =
        (rightIntersectionProjection rightPoint).phase p member

-- 全素相位源只给每个素数一个单位坐标; 它不是无限乘积对象。
structure AllPrimePhaseSource where
  phase : Nat -> RatComplex
  unit_phase :
    (p : Nat) -> IsPrime p -> RatEq (ratComplexNormSq (phase p)) ratOne

def allPrimePhaseFinitePoint
    (source : AllPrimePhaseSource) (window : PrimeWindow) :
    FinitePrimeTorusPoint window where
  phase := fun p _member => source.phase p
  unit_phase := fun p member =>
    source.unit_phase p (All.mem window.all_prime member)

theorem allPrimePhaseFiniteCoordinate_unit
    (source : AllPrimePhaseSource) (window : PrimeWindow)
    (p : Nat) (member : window.mem p) :
    RatEq
      (ratComplexNormSq
        ((allPrimePhaseFinitePoint source window).phase p member))
      ratOne := by
  exact source.unit_phase p (All.mem window.all_prime member)

theorem allPrimePhaseSource_projection_compatible
    (source : AllPrimePhaseSource)
    {small large : PrimeWindow}
    (incl : WindowInclusion small large) :
    FiniteProjectionCompatible incl
      (allPrimePhaseFinitePoint source small)
      (allPrimePhaseFinitePoint source large) := by
  constructor
  intro p member
  rfl

theorem allPrimePhaseSource_overlap_compatible
    (source : AllPrimePhaseSource)
    (left right : PrimeWindow) :
    FiniteSubtorusOverlapCompatible
      (allPrimePhaseFinitePoint source left)
      (allPrimePhaseFinitePoint source right) := by
  constructor
  intro p member
  rfl

-- 无限素数环面在 Lean 侧只作为有限窗口相容族接口出现。
structure PrimeTorusCompatibleSystem where
  point : (window : PrimeWindow) -> FinitePrimeTorusPoint window
  compatible :
    (small large : PrimeWindow) ->
      (incl : WindowInclusion small large) ->
        FiniteProjectionCompatible incl (point small) (point large)

def allPrimePhaseCompatibleSystem
    (source : AllPrimePhaseSource) : PrimeTorusCompatibleSystem where
  point := fun window => allPrimePhaseFinitePoint source window
  compatible := fun _small _large incl =>
    allPrimePhaseSource_projection_compatible source incl

theorem compatibleSystem_projected_coordinate
    (system : PrimeTorusCompatibleSystem)
    {small large : PrimeWindow}
    (incl : WindowInclusion small large)
    (p : Nat) (member : small.mem p) :
    (system.point small).phase p member =
      (system.point large).phase p (incl p member) := by
  exact (system.compatible small large incl).projected_eq p member

theorem allPrimePhaseCompatibleSystem_coordinate
    (source : AllPrimePhaseSource)
    (window : PrimeWindow)
    (p : Nat) (member : window.mem p) :
    ((allPrimePhaseCompatibleSystem source).point window).phase p member =
      source.phase p := by
  rfl

theorem allPrimePhaseCompatibleSystem_window_unit
    (source : AllPrimePhaseSource)
    (window : PrimeWindow)
    (p : Nat) (member : window.mem p) :
    RatEq
      (ratComplexNormSq
        (((allPrimePhaseCompatibleSystem source).point window).phase p member))
      ratOne := by
  exact source.unit_phase p (All.mem window.all_prime member)

end BEDC.Derived.RHRoute.InfinitePrimeTorusCompatibility
