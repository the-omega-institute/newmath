import BEDC.Foundations.TriangleGenerationSystem

namespace BEDC.Foundations.TriRealization

open BEDC.Foundations.TriangleGenerationSystem

/-- α 上的三角代数: 五个生成算子, 让 TriAxisObjCode 能被解释成 α 值。 -/
structure TriAlgebra (α : Type u) where
  base : α
  dist : α → α
  time : α → α
  sym : α → α
  pair : α → α → α

/-- 把 code 在三角代数里解释成一个 α 值 (沿构造子递归)。 -/
def TriAlgebra.interp {α : Type u} (A : TriAlgebra α) : TriAxisObjCode → α
  | TriAxisObjCode.base => A.base
  | TriAxisObjCode.distinctionGen c => A.dist (A.interp c)
  | TriAxisObjCode.timeGen c => A.time (A.interp c)
  | TriAxisObjCode.symmetryGen c => A.sym (A.interp c)
  | TriAxisObjCode.pairGen l r => A.pair (A.interp l) (A.interp r)

/-- 防造假核心: x 被 code c 实现, 当且仅当 x 恰好是 c 的解释。
    realization 不是自由标签 -- 它把 x 钉死在 code 的生成解释上。 -/
def TriRealizes {α : Type u} (A : TriAlgebra α) (c : TriAxisObjCode) (x : α) : Prop :=
  x = A.interp c

theorem TriRealizes.interp_self {α : Type u} (A : TriAlgebra α) (c : TriAxisObjCode) :
    TriRealizes A c (A.interp c) := rfl

/-- 实现是函数性的: 一个 code 至多实现一个值。 -/
theorem TriRealizes.unique {α : Type u} {A : TriAlgebra α} {c : TriAxisObjCode} {x y : α}
    (hx : TriRealizes A c x) (hy : TriRealizes A c y) : x = y := by
  unfold TriRealizes at hx hy
  rw [hx, hy]

/-- 被实现的值 (经 code 的强制唯一投影) 决定其三轴 profile。把 realization 连到
    (distinction,time,symmetry)。 -/
def realizedProfile {α : Type u} (_A : TriAlgebra α) (c : TriAxisObjCode) :
    TriAxisProfile := triAxisProjection c

/-- Nat 是典范的纯 time 代数: 时间轴上是 succ, 其余轴平凡。 -/
def natAlgebra : TriAlgebra Nat where
  base := 0
  dist := fun n => n
  time := Nat.succ
  sym := fun n => n
  pair := fun m n => m + n

theorem interp_natAsObjCode : ∀ n : Nat, natAlgebra.interp (natAsObjCode n) = n
  | 0 => rfl
  | n + 1 => by
      show natAlgebra.time (natAlgebra.interp (natAsObjCode n)) = n + 1
      rw [interp_natAsObjCode n]
      rfl

/-- Nat 的每个 n 被它的 time-code natAsObjCode n 真实现 (非贴标签)。 -/
theorem nat_realizes (n : Nat) : TriRealizes natAlgebra (natAsObjCode n) n :=
  (interp_natAsObjCode n).symm

/-- 反 vacuity 见证: timeGen base 只实现 A.time A.base, 不实现任意 x。
    这堵住"所有对象都贴 timeGen base"的造假。 -/
theorem timeGen_base_realizes_iff {α : Type u} (A : TriAlgebra α) (x : α) :
    TriRealizes A (TriAxisObjCode.timeGen TriAxisObjCode.base) x ↔ x = A.time A.base :=
  Iff.rfl

end BEDC.Foundations.TriRealization
