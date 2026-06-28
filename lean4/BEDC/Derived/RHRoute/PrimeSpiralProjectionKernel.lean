import BEDC.Derived.RHRoute.PrimePhaseRadialReadback

namespace BEDC.Derived.RHRoute.PrimeSpiralProjectionKernel

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat := BEDC.Derived.RationalUp.RatNum
abbrev RatComplex := BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex
abbrev PrimePhaseSample :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseSample
abbrev PrimePhaseRadialStructure :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseRadialStructure
abbrev PrimePhaseRadialReadback :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseRadialReadback

/-!
“螺旋”只标记 prime-indexed phase-radial row 的纸面隐喻。
本模块编码有限 prime phase readback 到有理复平面的投影核, 不编码共同周期、
无限能量、零点相关边界或 RH 结论。
-/

def RatComplexEq (z w : RatComplex) : Prop :=
  RatEq z.re w.re ∧ RatEq z.im w.im

theorem RatComplexEq_refl (z : RatComplex) : RatComplexEq z z := by
  exact And.intro (RatEq_refl z.re) (RatEq_refl z.im)

theorem RatComplexEq_symm {z w : RatComplex} :
    RatComplexEq z w -> RatComplexEq w z := by
  intro same
  exact And.intro (RatEq_symm same.left) (RatEq_symm same.right)

theorem RatComplexEq_trans (z w u : RatComplex) :
    RatComplexEq z w -> RatComplexEq w u -> RatComplexEq z u := by
  intro zw wu
  exact And.intro
    (RatEq_trans z.re w.re u.re zw.left wu.left)
    (RatEq_trans z.im w.im u.im zw.right wu.right)

def primeSpiralProjectionOfRat (q : Rat) : RatComplex :=
  { re := q, im := ratZero }

def primeSpiralProjection (readback : PrimePhaseRadialReadback) :
    RatComplex :=
  primeSpiralProjectionOfRat readback.readback

def PrimeSpiralProjectionZero
    (readback : PrimePhaseRadialReadback) : Prop :=
  RatComplexEq (primeSpiralProjection readback) ratComplexZero

def PrimeSpiralProjectionKernel
    (readback : PrimePhaseRadialReadback) : Prop :=
  RatEq readback.readback ratZero

def primeSpiralNormalHeight
    (readback : PrimePhaseRadialReadback) : Rat :=
  ratComplexNormSq (primeSpiralProjection readback)

structure PrimeSpiralProjectionPacket where
  surface : PrimePhaseRadialStructure
  readback : PrimePhaseRadialReadback
  readback_surface : readback.surface = surface
  projection : RatComplex
  projection_eq : RatComplexEq projection (primeSpiralProjection readback)

def projectionPacketFromReadback
    (readback : PrimePhaseRadialReadback) : PrimeSpiralProjectionPacket where
  surface := readback.surface
  readback := readback
  readback_surface := rfl
  projection := primeSpiralProjection readback
  projection_eq := RatComplexEq_refl _

theorem primeSpiralProjection_kernel_iff_zero
    (readback : PrimePhaseRadialReadback) :
    PrimeSpiralProjectionKernel readback ↔
      PrimeSpiralProjectionZero readback := by
  constructor
  · intro kernel
    exact And.intro kernel (RatEq_refl ratZero)
  · intro zero
    exact zero.left

theorem primeSpiralProjection_from_readback_exact
    (readback : PrimePhaseRadialReadback) :
    RatComplexEq
      (projectionPacketFromReadback readback).projection
      (primeSpiralProjection readback) := by
  exact RatComplexEq_refl _

theorem primeSpiralProjection_determined_by_readback
    {surface : PrimePhaseRadialStructure}
    (left right : PrimePhaseRadialReadback)
    (left_surface : left.surface = surface)
    (right_surface : right.surface = surface) :
    RatComplexEq (primeSpiralProjection left)
      (primeSpiralProjection right) := by
  have sameReadback : RatEq left.readback right.readback :=
    BEDC.Derived.RHRoute.PrimePhaseRadialReadback.readback_deterministic
      left right left_surface right_surface
  exact And.intro sameReadback (RatEq_refl ratZero)

theorem primeSpiralProjection_packet_deterministic
    {surface : PrimePhaseRadialStructure}
    (left right : PrimeSpiralProjectionPacket)
    (left_surface : left.surface = surface)
    (right_surface : right.surface = surface) :
    RatComplexEq left.projection right.projection := by
  have leftReadbackSurface : left.readback.surface = surface := by
    cases left_surface
    exact left.readback_surface
  have rightReadbackSurface : right.readback.surface = surface := by
    cases right_surface
    exact right.readback_surface
  have sameProjectedReadbacks :
      RatComplexEq (primeSpiralProjection left.readback)
        (primeSpiralProjection right.readback) :=
    primeSpiralProjection_determined_by_readback left.readback right.readback
      leftReadbackSurface rightReadbackSurface
  exact RatComplexEq_trans left.projection
    (primeSpiralProjection left.readback) right.projection
    left.projection_eq
    (RatComplexEq_trans (primeSpiralProjection left.readback)
      (primeSpiralProjection right.readback) right.projection
      sameProjectedReadbacks (RatComplexEq_symm right.projection_eq))

theorem primeSpiralProjection_packet_kernel_readback
    (packet : PrimeSpiralProjectionPacket) :
    PrimeSpiralProjectionKernel packet.readback ->
      RatComplexEq packet.projection ratComplexZero := by
  intro kernel
  have zeroProjection :
      PrimeSpiralProjectionZero packet.readback :=
    (primeSpiralProjection_kernel_iff_zero packet.readback).mp kernel
  exact RatComplexEq_trans packet.projection
    (primeSpiralProjection packet.readback) ratComplexZero
    packet.projection_eq zeroProjection

theorem primeSpiralProjection_single_kernel_exact :
    PrimeSpiralProjectionKernel
      BEDC.Derived.RHRoute.PrimePhaseRadialReadback.singlePrimePhaseRadialReadback ↔
      PrimeSpiralProjectionZero
        BEDC.Derived.RHRoute.PrimePhaseRadialReadback.singlePrimePhaseRadialReadback := by
  exact primeSpiralProjection_kernel_iff_zero
    BEDC.Derived.RHRoute.PrimePhaseRadialReadback.singlePrimePhaseRadialReadback

end BEDC.Derived.RHRoute.PrimeSpiralProjectionKernel
