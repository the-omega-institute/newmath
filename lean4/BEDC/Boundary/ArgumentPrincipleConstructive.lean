import BEDC.Derived.RationalUp

namespace BEDC.Boundary.ArgumentPrincipleConstructive

open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

structure RatComplex where
  re : Rat
  im : Rat

structure RatInterval where
  lo : Rat
  hi : Rat
  proper : ratLt lo hi

structure RatRect where
  re : RatInterval
  im : RatInterval

def RatRect.Subset (inner outer : RatRect) : Prop :=
  ratLe outer.re.lo inner.re.lo ∧
    ratLe inner.re.hi outer.re.hi ∧
      ratLe outer.im.lo inner.im.lo ∧
        ratLe inner.im.hi outer.im.hi

structure RatTube where
  re : RatInterval
  im : RatInterval

structure BoundarySegment (Point : Type u) where
  point : Rat -> Point
  parameterInSegment : Rat -> Prop

structure LocatedComplex where
  rect : Nat -> RatRect

structure ZetaBoundaryInterface where
  Point : Type
  zero : Point
  zeta : Point -> Point
  rectBoundary : RatRect -> BoundarySegment Point
  winding : (Point -> Point) -> BoundarySegment Point -> Int
  zeroCount : (Point -> Point) -> RatRect -> Nat
  apartFromZeroOnBoundary : (Point -> Point) -> RatRect -> Prop
  inTube : Point -> RatTube -> Prop
  tubeApartFromZero : RatTube -> Prop
  locatedPoint : LocatedComplex -> Point
  locatedApproxEq : Point -> Point -> Prop
  nestedRectStream : LocatedComplex -> Prop
  rectIndexOne : RatRect -> Prop

-- 构造性 argument principle 需要 mathlib-free 复分析与 Brouwer degree。
-- 本文件只在 BEDC/Boundary 记录命题边界；0-axiom 主构造只依赖有限 winding cert 层。
def argumentPrinciple_rect
    (I : ZetaBoundaryInterface) (R : RatRect)
    (_hBoundary : I.apartFromZeroOnBoundary I.zeta R) : Prop :=
  I.winding I.zeta (I.rectBoundary R) = Int.ofNat (I.zeroCount I.zeta R)

-- 段 enclosure 必须控制整段，而不是只控制有限点值 box。
-- 需要 segment interval evaluator 或点值加 Lipschitz；仅有点值 box 不推出边界 apartness。
def zetaSegmentUniformEnclosure
    (I : ZetaBoundaryInterface) (segment : BoundarySegment I.Point)
    (tube : RatTube) : Prop :=
  (∀ t : Rat, segment.parameterInSegment t ->
    I.inTube (I.zeta (segment.point t)) tube) ∧
      I.tubeApartFromZero tube

-- nested index-one 只给出语义零点等式的分析边界，不在这里证明 ζ(located ρ)≈0。
-- 推出该等式需要 A 层有限证书、B 层 argument principle 与连续性。
def rho_near_14_1347_semanticZero
    (I : ZetaBoundaryInterface) (rho_near_14_1347 : LocatedComplex) : Prop :=
  I.nestedRectStream rho_near_14_1347 ∧
      (∀ n : Nat, I.rectIndexOne (rho_near_14_1347.rect n)) ->
    I.locatedApproxEq (I.zeta (I.locatedPoint rho_near_14_1347)) I.zero

end BEDC.Boundary.ArgumentPrincipleConstructive
