import BEDC.Derived.OnticCollapseModes

namespace BEDC.Derived.TimeFibreMirrorAtomicityUp

open BEDC.Derived.OnticCollapseModes

/-!
时间纤维镜像原子性只记录本体三轴里的 Time 行、Atom 行与
函数方程镜像行。这里不声明 RH 支撑、几何边界或解析零点定理。
-/

universe u

structure TimeFibreCoordinate (O : OnticPacket.{u}) : Sort (max 1 u) where
  normal : O.Atom
  time : O.Time

structure TimeFibreMirror (O : OnticPacket.{u}) : Sort (max 1 u) where
  normalMirror : O.Atom -> O.Atom
  normalMirror_involutive :
    ∀ normal : O.Atom, normalMirror (normalMirror normal) = normal

namespace TimeFibreMirror

variable {O : OnticPacket.{u}}

def coordinate (mirror : TimeFibreMirror O)
    (point : TimeFibreCoordinate O) : TimeFibreCoordinate O where
  normal := mirror.normalMirror point.normal
  time := point.time

theorem coordinate_time_preserved
    (mirror : TimeFibreMirror O) (point : TimeFibreCoordinate O) :
    (mirror.coordinate point).time = point.time := by
  rfl

theorem coordinate_normal_reflected
    (mirror : TimeFibreMirror O) (point : TimeFibreCoordinate O) :
    (mirror.coordinate point).normal = mirror.normalMirror point.normal := by
  rfl

theorem coordinate_involutive
    (mirror : TimeFibreMirror O) (point : TimeFibreCoordinate O) :
    mirror.coordinate (mirror.coordinate point) = point := by
  cases point with
  | mk normal time =>
      change { normal := mirror.normalMirror (mirror.normalMirror normal), time := time } =
        ({ normal := normal, time := time } : TimeFibreCoordinate O)
      rw [mirror.normalMirror_involutive normal]

end TimeFibreMirror

structure TimeFibreAtom (O : OnticPacket.{u}) : Sort (max 1 u) where
  zeroAt : O.Time -> O.Atom -> Prop
  unique :
    ∀ {time : O.Time} {left right : O.Atom},
      zeroAt time left -> zeroAt time right -> left = right

namespace TimeFibreAtom

variable {O : OnticPacket.{u}}

def zeroCoordinate (atom : TimeFibreAtom O)
    (point : TimeFibreCoordinate O) : Prop :=
  atom.zeroAt point.time point.normal

theorem same_time_zero_unique
    (atom : TimeFibreAtom O) {time : O.Time} {left right : O.Atom} :
    atom.zeroAt time left -> atom.zeroAt time right -> left = right := by
  intro leftZero rightZero
  exact atom.unique leftZero rightZero

theorem coordinate_zero_unique
    (atom : TimeFibreAtom O) {left right : TimeFibreCoordinate O} :
    left.time = right.time ->
      atom.zeroCoordinate left ->
        atom.zeroCoordinate right ->
          left.normal = right.normal := by
  intro sameTime leftZero rightZero
  cases left with
  | mk leftNormal leftTime =>
      cases right with
      | mk rightNormal rightTime =>
          change leftTime = rightTime at sameTime
          change atom.zeroAt leftTime leftNormal at leftZero
          change atom.zeroAt rightTime rightNormal at rightZero
          rw [sameTime] at leftZero
          exact atom.unique leftZero rightZero

end TimeFibreAtom

structure TimeFibreMirrorClosure (O : OnticPacket.{u})
    (atom : TimeFibreAtom O) (mirror : TimeFibreMirror O) :
    Sort (max 1 u) where
  mirror_zero :
    ∀ {time : O.Time} {normal : O.Atom},
      atom.zeroAt time normal -> atom.zeroAt time (mirror.normalMirror normal)

namespace TimeFibreMirrorClosure

variable {O : OnticPacket.{u}}
variable {atom : TimeFibreAtom O} {mirror : TimeFibreMirror O}

theorem companion_same_fibre
    (closure : TimeFibreMirrorClosure O atom mirror)
    {time : O.Time} {normal : O.Atom} :
    atom.zeroAt time normal ->
      atom.zeroAt time (mirror.normalMirror normal) := by
  intro zero
  exact closure.mirror_zero zero

theorem mirror_companion_unique
    (closure : TimeFibreMirrorClosure O atom mirror)
    {time : O.Time} {normal : O.Atom} :
    atom.zeroAt time normal -> mirror.normalMirror normal = normal := by
  intro zero
  exact atom.unique (closure.mirror_zero zero) zero

end TimeFibreMirrorClosure

structure TimeFibreAtomicity (O : OnticPacket.{u}) : Sort (max 1 u) where
  atom : TimeFibreAtom O
  mirror : TimeFibreMirror O
  closure : TimeFibreMirrorClosure O atom mirror
  noTimeCollapse : TimeCollapse O.Time -> False

namespace TimeFibreAtomicity

variable {O : OnticPacket.{u}}

theorem zero_unique
    (packet : TimeFibreAtomicity O) {time : O.Time} {left right : O.Atom} :
    packet.atom.zeroAt time left ->
      packet.atom.zeroAt time right ->
        left = right := by
  intro leftZero rightZero
  exact packet.atom.unique leftZero rightZero

theorem mirror_zero
    (packet : TimeFibreAtomicity O) {time : O.Time} {normal : O.Atom} :
    packet.atom.zeroAt time normal ->
      packet.atom.zeroAt time (packet.mirror.normalMirror normal) := by
  intro zero
  exact packet.closure.mirror_zero zero

theorem mirror_companion_unique
    (packet : TimeFibreAtomicity O) {time : O.Time} {normal : O.Atom} :
    packet.atom.zeroAt time normal ->
      packet.mirror.normalMirror normal = normal := by
  intro zero
  exact packet.atom.unique (packet.mirror_zero zero) zero

theorem rejects_timeCollapse
    (packet : TimeFibreAtomicity O) :
    TimeCollapse O.Time -> False := by
  intro collapse
  exact packet.noTimeCollapse collapse

theorem to_nonCollapsePacket
    (packet : TimeFibreAtomicity O)
    (noSymmetry : SymCollapse O.Symmetry -> False)
    (noDistinction : DistCollapse -> False) :
    NonCollapsePacket O where
  noTime := packet.rejects_timeCollapse
  noSymmetry := noSymmetry
  noDistinction := noDistinction

end TimeFibreAtomicity

end BEDC.Derived.TimeFibreMirrorAtomicityUp
