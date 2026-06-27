import BEDC.Derived.NonCollapseInvariantUp

namespace BEDC.Derived.OnticCollapseModes

/-!
本文件只编码三种 collapse 的类型形状与本体三轴路由。
它只记录可由本地假设推出的结论形状，不注册外部逻辑原则。
-/

universe u

inductive OnticAxis where
  | time
  | symmetry
  | distinction

inductive CollapseMode where
  | timeCollapse
  | symCollapse
  | distCollapse

def axisOf : CollapseMode -> OnticAxis
  | CollapseMode.timeCollapse => OnticAxis.time
  | CollapseMode.symCollapse => OnticAxis.symmetry
  | CollapseMode.distCollapse => OnticAxis.distinction

def TimeCollapse (α : Sort u) : Sort (max 1 u) :=
  ∀ {P : α -> Prop}, (∃ x : α, P x) -> Subtype P

structure FiberClassToken (α : Sort u) (r : α -> α -> Prop) where
  point : α

def FiberClassEq {α : Sort u} {r : α -> α -> Prop}
    (a b : FiberClassToken α r) : Prop :=
  a = b

def SymCollapse (α : Sort u) : Prop :=
  ∀ {r : α -> α -> Prop} {x y : α},
    r x y ->
      FiberClassEq
        (r := r)
        ({ point := x } : FiberClassToken α r)
        ({ point := y } : FiberClassToken α r)

def DistCollapse : Prop :=
  ∀ {P Q : Prop}, (P ↔ Q) -> P = Q

structure OnticPacket where
  Atom : Sort u
  Time : Sort u
  Symmetry : Sort u

structure LocatedOnticPacket extends OnticPacket.{u} where
  atomLocated : Atom -> Prop
  timeLocated : Time -> Prop
  symmetryLocated : Symmetry -> Prop

structure CollapsePacket (O : OnticPacket.{u}) : Sort (max 1 u) where
  time : TimeCollapse O.Time
  symmetry : SymCollapse O.Symmetry
  distinction : DistCollapse

structure NonCollapsePacket (O : OnticPacket.{u}) : Prop where
  noTime : TimeCollapse O.Time -> False
  noSymmetry : SymCollapse O.Symmetry -> False
  noDistinction : DistCollapse -> False

structure BoxStreamOnticNonCollapseLink where
  witness : BEDC.Derived.NonCollapseInvariantUp.BoxStreamNonCollapseWitness
  packet : OnticPacket
  noExactRatRetraction :
    BEDC.Derived.NonCollapseInvariantUp.BoxStreamExactRatRetraction
      witness.gauge witness.point -> False

def boxStreamOnticPacket
    (witness : BEDC.Derived.NonCollapseInvariantUp.BoxStreamNonCollapseWitness) :
    OnticPacket where
  Atom := BEDC.Derived.RationalUp.RatNum
  Time := Nat
  Symmetry := BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxStream witness.gauge

def boxStreamOnticNonCollapseLink
    (witness : BEDC.Derived.NonCollapseInvariantUp.BoxStreamNonCollapseWitness) :
    BoxStreamOnticNonCollapseLink where
  witness := witness
  packet := boxStreamOnticPacket witness
  noExactRatRetraction :=
    BEDC.Derived.NonCollapseInvariantUp.BoxStreamNonCollapseWitness.no_rat_retraction
      witness

def NoCollapseAssumptions (O : OnticPacket.{u}) : Prop :=
  (TimeCollapse O.Time -> False) ∧
    (SymCollapse O.Symmetry -> False) ∧
      (DistCollapse -> False)

def timeCollapse_witness_shape {α : Sort u}
    (collapse : TimeCollapse α) {P : α -> Prop} :
    (∃ x : α, P x) -> Subtype P := by
  intro h
  exact collapse h

theorem symCollapse_fiber_sound_shape {α : Sort u}
    (collapse : SymCollapse α) {r : α -> α -> Prop} {x y : α} :
    r x y ->
      FiberClassEq
        (r := r)
        ({ point := x } : FiberClassToken α r)
        ({ point := y } : FiberClassToken α r) := by
  intro h
  exact collapse h

theorem distCollapse_equality_shape
    (collapse : DistCollapse) {P Q : Prop} :
    (P ↔ Q) -> P = Q := by
  intro h
  exact collapse h

theorem timeCollapse_axis :
    axisOf CollapseMode.timeCollapse = OnticAxis.time := by
  rfl

theorem symCollapse_axis :
    axisOf CollapseMode.symCollapse = OnticAxis.symmetry := by
  rfl

theorem distCollapse_axis :
    axisOf CollapseMode.distCollapse = OnticAxis.distinction := by
  rfl

theorem collapse_modes_are_axis_distinct :
    axisOf CollapseMode.timeCollapse = OnticAxis.time ∧
      axisOf CollapseMode.symCollapse = OnticAxis.symmetry ∧
        axisOf CollapseMode.distCollapse = OnticAxis.distinction := by
  exact ⟨rfl, rfl, rfl⟩

theorem onticAxis_time_ne_symmetry :
    OnticAxis.time = OnticAxis.symmetry -> False := by
  intro h
  cases h

theorem onticAxis_time_ne_distinction :
    OnticAxis.time = OnticAxis.distinction -> False := by
  intro h
  cases h

theorem onticAxis_symmetry_ne_distinction :
    OnticAxis.symmetry = OnticAxis.distinction -> False := by
  intro h
  cases h

theorem collapse_modes_axis_pairwise_distinct :
    (axisOf CollapseMode.timeCollapse = axisOf CollapseMode.symCollapse -> False) ∧
      (axisOf CollapseMode.timeCollapse = axisOf CollapseMode.distCollapse -> False) ∧
        (axisOf CollapseMode.symCollapse = axisOf CollapseMode.distCollapse -> False) := by
  exact ⟨onticAxis_time_ne_symmetry,
    onticAxis_time_ne_distinction,
    onticAxis_symmetry_ne_distinction⟩

theorem collapse_modes_cover_ontic_axes (mode : CollapseMode) :
    axisOf mode = OnticAxis.time ∨
      axisOf mode = OnticAxis.symmetry ∨
        axisOf mode = OnticAxis.distinction := by
  cases mode with
  | timeCollapse =>
      exact Or.inl rfl
  | symCollapse =>
      exact Or.inr (Or.inl rfl)
  | distCollapse =>
      exact Or.inr (Or.inr rfl)

theorem collapse_axis_complete (axis : OnticAxis) :
    ∃ mode : CollapseMode, axisOf mode = axis := by
  cases axis with
  | time =>
      exact ⟨CollapseMode.timeCollapse, rfl⟩
  | symmetry =>
      exact ⟨CollapseMode.symCollapse, rfl⟩
  | distinction =>
      exact ⟨CollapseMode.distCollapse, rfl⟩

theorem nonCollapsePacket_to_noCollapseAssumptions {O : OnticPacket.{u}} :
    NonCollapsePacket O -> NoCollapseAssumptions O := by
  intro h
  exact ⟨h.noTime, h.noSymmetry, h.noDistinction⟩

theorem noCollapseAssumptions_to_nonCollapsePacket {O : OnticPacket.{u}} :
    NoCollapseAssumptions O -> NonCollapsePacket O := by
  intro h
  exact {
    noTime := h.left
    noSymmetry := h.right.left
    noDistinction := h.right.right
  }

theorem noCollapseAssumptions_iff_nonCollapsePacket {O : OnticPacket.{u}} :
    NoCollapseAssumptions O ↔ NonCollapsePacket O := by
  exact ⟨noCollapseAssumptions_to_nonCollapsePacket,
    nonCollapsePacket_to_noCollapseAssumptions⟩

theorem nonCollapsePacket_rejects_collapsePacket {O : OnticPacket.{u}} :
    NonCollapsePacket O -> CollapsePacket O -> False := by
  intro noncollapse collapse
  exact noncollapse.noTime collapse.time

structure ExcludedCollapseShapePacket (O : OnticPacket.{u}) : Sort (max 1 u) where
  timeWitnessShape :
    TimeCollapse O.Time ->
      ∀ {P : O.Time -> Prop}, (∃ x : O.Time, P x) -> Subtype P
  symmetryFiberShape :
    SymCollapse O.Symmetry ->
      ∀ {r : O.Symmetry -> O.Symmetry -> Prop} {x y : O.Symmetry},
        r x y ->
            FiberClassEq
            (r := r)
            ({ point := x } : FiberClassToken O.Symmetry r)
            ({ point := y } : FiberClassToken O.Symmetry r)
  distinctionEqualityShape :
    DistCollapse ->
      ∀ {P Q : Prop}, (P ↔ Q) -> P = Q
  modeAxes :
    axisOf CollapseMode.timeCollapse = OnticAxis.time ∧
      axisOf CollapseMode.symCollapse = OnticAxis.symmetry ∧
        axisOf CollapseMode.distCollapse = OnticAxis.distinction

def excludedCollapseShapePacket (O : OnticPacket.{u}) :
    ExcludedCollapseShapePacket O := by
  exact {
    timeWitnessShape := by
      intro collapse
      exact timeCollapse_witness_shape collapse
    symmetryFiberShape := by
      intro collapse
      exact symCollapse_fiber_sound_shape collapse
    distinctionEqualityShape := by
      intro collapse
      exact distCollapse_equality_shape collapse
    modeAxes := collapse_modes_are_axis_distinct
  }

theorem excluded_axioms_are_collapse_modes (O : OnticPacket.{u}) :
    (∀ _collapse : TimeCollapse O.Time,
        ∀ {P : O.Time -> Prop},
          Nonempty ((∃ x : O.Time, P x) -> Subtype P)) ∧
      (∀ _collapse : SymCollapse O.Symmetry,
        ∀ {r : O.Symmetry -> O.Symmetry -> Prop} {x y : O.Symmetry},
          r x y ->
            FiberClassEq
              (r := r)
              ({ point := x } : FiberClassToken O.Symmetry r)
              ({ point := y } : FiberClassToken O.Symmetry r)) ∧
        (∀ _collapse : DistCollapse,
          ∀ {P Q : Prop}, (P ↔ Q) -> P = Q) ∧
          axisOf CollapseMode.timeCollapse = OnticAxis.time ∧
            axisOf CollapseMode.symCollapse = OnticAxis.symmetry ∧
              axisOf CollapseMode.distCollapse = OnticAxis.distinction := by
  exact ⟨
    (by
      intro collapse
      exact ⟨timeCollapse_witness_shape collapse⟩),
    (by
      exact ⟨
        (by
          intro collapse
          exact symCollapse_fiber_sound_shape collapse),
        (by
          exact ⟨
            (by
              intro collapse
              exact distCollapse_equality_shape collapse),
            collapse_modes_are_axis_distinct⟩)⟩)⟩

end BEDC.Derived.OnticCollapseModes
