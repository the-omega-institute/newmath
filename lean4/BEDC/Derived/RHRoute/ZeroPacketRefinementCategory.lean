import BEDC.Derived.RHRoute.LocatedZetaZero

namespace BEDC.Derived.RHRoute.ZeroPacketRefinementCategory

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.LocatedZetaZero

abbrev RatRect := LocatedZetaZero.RatRect
abbrev ZetaRectIndexCert := LocatedZetaZero.ZetaRectIndexCert
abbrev RefinementStep := LocatedZetaZero.RefinementStep

-- 零点包只携带有理矩形与 winding-index 证书；不声明解析延拓、
-- 辐角原理, 或 located 极限存在性。
structure ZeroPacket where
  rect : RatRect
  index : ZetaRectIndexCert rect 1

abbrev AtomicRefinement (source target : ZeroPacket) : Type :=
  RefinementStep source.rect target.rect

inductive RefinementPath : ZeroPacket -> ZeroPacket -> Type where
  | identity (packet : ZeroPacket) : RefinementPath packet packet
  | step {source middle target : ZeroPacket} :
      AtomicRefinement source target ->
        RefinementPath target middle ->
          RefinementPath source middle

namespace RefinementPath

def ofStep {source target : ZeroPacket}
    (step : AtomicRefinement source target) :
    RefinementPath source target :=
  RefinementPath.step step (RefinementPath.identity target)

def append {source middle target : ZeroPacket} :
    RefinementPath source middle ->
      RefinementPath middle target ->
        RefinementPath source target
  | RefinementPath.identity _, right => right
  | RefinementPath.step first tail, right =>
      RefinementPath.step first (append tail right)

def atomCount {source target : ZeroPacket} :
    RefinementPath source target -> Nat
  | RefinementPath.identity _ => 0
  | RefinementPath.step _ tail => Nat.succ (atomCount tail)

theorem append_left_identity {source target : ZeroPacket}
    (path : RefinementPath source target) :
    append (RefinementPath.identity source) path = path := by
  rfl

theorem append_right_identity {source target : ZeroPacket}
    (path : RefinementPath source target) :
    append path (RefinementPath.identity target) = path := by
  induction path with
  | identity packet =>
      rfl
  | step first tail ih =>
      change
        RefinementPath.step first
            (append tail (RefinementPath.identity _)) =
          RefinementPath.step first tail
      rw [ih]

theorem append_assoc {a b c d : ZeroPacket}
    (left : RefinementPath a b)
    (middle : RefinementPath b c)
    (right : RefinementPath c d) :
    append (append left middle) right =
      append left (append middle right) := by
  induction left with
  | identity packet =>
      rfl
  | step first tail ih =>
      change
        RefinementPath.step first (append (append tail middle) right) =
          RefinementPath.step first (append tail (append middle right))
      rw [ih]

theorem atomCount_append {source middle target : ZeroPacket}
    (left : RefinementPath source middle)
    (right : RefinementPath middle target) :
    atomCount (append left right) = atomCount left + atomCount right := by
  induction left with
  | identity packet =>
      change atomCount right = 0 + atomCount right
      exact Eq.symm (Nat.zero_add (atomCount right))
  | step first tail ih =>
      change
        Nat.succ (atomCount (append tail right)) =
          Nat.succ (atomCount tail) + atomCount right
      calc
        Nat.succ (atomCount (append tail right)) =
            Nat.succ (atomCount tail + atomCount right) := by
              rw [ih]
        _ = Nat.succ (atomCount tail) + atomCount right := by
              rw [Nat.succ_add]

end RefinementPath

def composeAtomic {source middle target : ZeroPacket}
    (left : AtomicRefinement source middle)
    (right : AtomicRefinement middle target) :
    RefinementPath source target :=
  RefinementPath.append
    (RefinementPath.ofStep left)
    (RefinementPath.ofStep right)

theorem composeAtomic_atomCount {source middle target : ZeroPacket}
    (left : AtomicRefinement source middle)
    (right : AtomicRefinement middle target) :
    RefinementPath.atomCount (composeAtomic left right) = 2 := by
  rfl

structure RefinementCategory where
  Obj : Type
  Hom : Obj -> Obj -> Type
  identity : (x : Obj) -> Hom x x
  compose : {x y z : Obj} -> Hom x y -> Hom y z -> Hom x z
  left_identity :
    {x y : Obj} -> (f : Hom x y) ->
      compose (identity x) f = f
  right_identity :
    {x y : Obj} -> (f : Hom x y) ->
      compose f (identity y) = f
  assoc :
    {w x y z : Obj} ->
      (f : Hom w x) -> (g : Hom x y) -> (h : Hom y z) ->
        compose (compose f g) h = compose f (compose g h)

def zeroPacketRefinementCategory : RefinementCategory where
  Obj := ZeroPacket
  Hom := RefinementPath
  identity := RefinementPath.identity
  compose := RefinementPath.append
  left_identity := by
    intro x y f
    exact RefinementPath.append_left_identity f
  right_identity := by
    intro x y f
    exact RefinementPath.append_right_identity f
  assoc := by
    intro w x y z f g h
    exact RefinementPath.append_assoc f g h

theorem zeroPacketRefinementCategory_left_identity
    {source target : ZeroPacket}
    (path : RefinementPath source target) :
    zeroPacketRefinementCategory.compose
      (zeroPacketRefinementCategory.identity source) path = path :=
  zeroPacketRefinementCategory.left_identity path

theorem zeroPacketRefinementCategory_right_identity
    {source target : ZeroPacket}
    (path : RefinementPath source target) :
    zeroPacketRefinementCategory.compose path
      (zeroPacketRefinementCategory.identity target) = path :=
  zeroPacketRefinementCategory.right_identity path

theorem zeroPacketRefinementCategory_assoc
    {a b c d : ZeroPacket}
    (left : RefinementPath a b)
    (middle : RefinementPath b c)
    (right : RefinementPath c d) :
    zeroPacketRefinementCategory.compose
        (zeroPacketRefinementCategory.compose left middle) right =
      zeroPacketRefinementCategory.compose left
        (zeroPacketRefinementCategory.compose middle right) :=
  zeroPacketRefinementCategory.assoc left middle right

namespace Boundary

-- 把两个原子 refinement 压回一个直接 `RefinementStep` 需要额外的
-- 矩形包含与宽度收缩证据；这里显式作为 BEDC/Boundary 数据输入。
structure DirectStepCompositeData
    {source middle target : ZeroPacket}
    (_left : AtomicRefinement source middle)
    (_right : AtomicRefinement middle target) where
  subset : target.rect.Subset source.rect
  shrinkRe :
    ratLe target.rect.reWidth
      (ratMul source.rect.reWidth LocatedZetaZero.half)
  shrinkIm :
    ratLe target.rect.imWidth
      (ratMul source.rect.imWidth LocatedZetaZero.half)
  childIndex : ZetaRectIndexCert target.rect 1

def composeDirect {source middle target : ZeroPacket}
    (left : AtomicRefinement source middle)
    (right : AtomicRefinement middle target)
    (boundary : DirectStepCompositeData left right) :
    AtomicRefinement source target :=
  { subset := boundary.subset
    shrinkRe := boundary.shrinkRe
    shrinkIm := boundary.shrinkIm
    childIndex := boundary.childIndex }

theorem composeDirect_childIndex {source middle target : ZeroPacket}
    (left : AtomicRefinement source middle)
    (right : AtomicRefinement middle target)
    (boundary : DirectStepCompositeData left right) :
    (composeDirect left right boundary).childIndex = boundary.childIndex := by
  rfl

end Boundary

end BEDC.Derived.RHRoute.ZeroPacketRefinementCategory
