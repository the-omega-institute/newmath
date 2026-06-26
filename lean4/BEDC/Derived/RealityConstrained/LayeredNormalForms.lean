namespace BEDC.RealityConstrained

/--
读出系统把源对象投影到公开读出，并把不可见部分保留为每个读出
上的 fiber。`realize` 与 `read_realize` 表示 fiber 行可回读到同一公开面。
-/
structure ReadoutSystem (Source Readout : Type) where
  read : Source → Readout
  Fiber : Readout → Type
  realize : (r : Readout) → Fiber r → Source
  read_realize : (r : Readout) → (f : Fiber r) → read (realize r f) = r

namespace ReadoutSystem

theorem realize_readback {Source Readout : Type} (L : ReadoutSystem Source Readout)
    (r : Readout) (f : L.Fiber r) : L.read (L.realize r f) = r :=
  L.read_realize r f

end ReadoutSystem

/--
层扩张是两个读出系统之间的交换方块。`forget` 回到旧源层，
`readForget` 回到旧读出层，`commutes` 是源读出与读出回忘的一致性。
-/
structure LayerExtension (S₀ R₀ S₁ R₁ : Type)
    (L₀ : ReadoutSystem S₀ R₀) (L₁ : ReadoutSystem S₁ R₁) where
  forget : S₁ → S₀
  readForget : R₁ → R₀
  commutes : (x : S₁) → L₀.read (forget x) = readForget (L₁.read x)

namespace LayerExtension

theorem read_forget_commutes {S₀ R₀ S₁ R₁ : Type}
    {L₀ : ReadoutSystem S₀ R₀} {L₁ : ReadoutSystem S₁ R₁}
    (E : LayerExtension S₀ R₀ S₁ R₁ L₀ L₁) (x : S₁) :
    L₀.read (E.forget x) = E.readForget (L₁.read x) :=
  E.commutes x

theorem realized_fiber_commutes {S₀ R₀ S₁ R₁ : Type}
    {L₀ : ReadoutSystem S₀ R₀} {L₁ : ReadoutSystem S₁ R₁}
    (E : LayerExtension S₀ R₀ S₁ R₁ L₀ L₁) (r : R₁) (f : L₁.Fiber r) :
    L₀.read (E.forget (L₁.realize r f)) = E.readForget r := by
  rw [E.commutes (L₁.realize r f), L₁.read_realize r f]

end LayerExtension

/--
所谓 orthogonal axis 在这里仅表示 product-like normal form：对象由左右两条
显式坐标轴打包，投影回读各自坐标。它不含 Hilbert 空间或内积语义。
-/
structure AxisProductNormalForm (S A B : Type) where
  left : S → A
  right : S → B
  pack : A → B → S
  left_pack : (a : A) → (b : B) → left (pack a b) = a
  right_pack : (a : A) → (b : B) → right (pack a b) = b

namespace AxisProductNormalForm

theorem left_readback {S A B : Type} (N : AxisProductNormalForm S A B)
    (a : A) (b : B) : N.left (N.pack a b) = a :=
  N.left_pack a b

theorem right_readback {S A B : Type} (N : AxisProductNormalForm S A B)
    (a : A) (b : B) : N.right (N.pack a b) = b :=
  N.right_pack a b

theorem packed_readback {S A B : Type} (N : AxisProductNormalForm S A B)
    (a : A) (b : B) : N.left (N.pack a b) = a ∧ N.right (N.pack a b) = b :=
  And.intro (N.left_pack a b) (N.right_pack a b)

end AxisProductNormalForm

/--
近似塔只记录相邻截断、每层自然数读出，以及细层读出经 coarseReadout
后与粗层截断读出一致。这里的 `coarseReadout` 是外部给定的可计算读出降阶行。
-/
structure ApproximationTower (coarseReadout : Nat → Nat) where
  Approx : Nat → Type
  trunc : (n : Nat) → Approx (n + 1) → Approx n
  readout : (n : Nat) → Approx n → Nat
  refinement_sound :
    (n : Nat) → (x : Approx (n + 1)) →
      readout n (trunc n x) = coarseReadout (readout (n + 1) x)

namespace ApproximationTower

theorem trunc_readout_sound {coarseReadout : Nat → Nat}
    (T : ApproximationTower coarseReadout) (n : Nat) (x : T.Approx (n + 1)) :
    T.readout n (T.trunc n x) = coarseReadout (T.readout (n + 1) x) :=
  T.refinement_sound n x

end ApproximationTower

end BEDC.RealityConstrained
