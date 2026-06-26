import BEDC.Derived.RealityConstrained.LayeredNormalForms

namespace BEDC.RealityConstrained

/--
信息生成 witness 是有限读出步骤的全部构造性证据：生成读出带有
fiber 回读到源对象，且有一条对旧读出不可见、对新读出可见的分离行。
`preserves` 记录旧读出已经可分辨的源对在新读出中仍可分辨。
-/
structure InfoGenWitness {Source Readout : Type}
    (L : ReadoutSystem Source Readout)
    (Distinguishes : Readout → Source → Source → Prop)
    (source : Source) (previous generated : Readout) where
  fiber : L.Fiber generated
  source_readback : source = L.realize generated fiber
  comparison : Source
  generated_separates : Distinguishes generated source comparison
  previous_not_separates : Distinguishes previous source comparison → False
  preserves :
    (left right : Source) →
      Distinguishes previous left right → Distinguishes generated left right

namespace InfoGenWitness

theorem readback_consistent {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    {source : Source} {previous generated : Readout}
    (w : InfoGenWitness L Distinguishes source previous generated) :
    L.read source = generated := by
  rw [w.source_readback]
  exact L.read_realize generated w.fiber

theorem new_distinction {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    {source : Source} {previous generated : Readout}
    (w : InfoGenWitness L Distinguishes source previous generated) :
    Distinguishes generated source w.comparison ∧
      (Distinguishes previous source w.comparison → False) :=
  And.intro w.generated_separates w.previous_not_separates

end InfoGenWitness

/--
单个构造性信息生成步骤：从一个源对象出发，给出旧读出、新读出，
以及把新读出回读到源对象并保持旧分离关系的 witness。
-/
structure InfoGenStep {Source Readout : Type}
    (L : ReadoutSystem Source Readout)
    (Distinguishes : Readout → Source → Source → Prop) where
  source : Source
  previous : Readout
  generated : Readout
  witness : InfoGenWitness L Distinguishes source previous generated

namespace InfoGenStep

theorem readback_consistent {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (step : InfoGenStep L Distinguishes) :
    L.read step.source = step.generated :=
  InfoGenWitness.readback_consistent step.witness

theorem info_monotone {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (step : InfoGenStep L Distinguishes) :
    (left right : Source) →
      Distinguishes step.previous left right →
        Distinguishes step.generated left right :=
  step.witness.preserves

theorem new_distinction {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (step : InfoGenStep L Distinguishes) :
    Distinguishes step.generated step.source step.witness.comparison ∧
      (Distinguishes step.previous step.source step.witness.comparison → False) :=
  InfoGenWitness.new_distinction step.witness

end InfoGenStep

/--
相邻步骤的 readout 链接。空 trace 和单步 trace 是有限边界情形；
两步以上必须让前一步生成的读出成为后一步的旧读出。
-/
inductive TraceLinked {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop} :
    List (InfoGenStep L Distinguishes) → Prop where
  | nil : TraceLinked []
  | single (step : InfoGenStep L Distinguishes) : TraceLinked [step]
  | cons {first second : InfoGenStep L Distinguishes}
      {rest : List (InfoGenStep L Distinguishes)} :
      first.generated = second.previous →
        TraceLinked (second :: rest) →
          TraceLinked (first :: second :: rest)

namespace TraceLinked

theorem adjacent {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    {first second : InfoGenStep L Distinguishes}
    {rest : List (InfoGenStep L Distinguishes)}
    (linked : TraceLinked (first :: second :: rest)) :
    first.generated = second.previous := by
  cases linked with
  | cons link _ => exact link

theorem tail {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    {first second : InfoGenStep L Distinguishes}
    {rest : List (InfoGenStep L Distinguishes)}
    (linked : TraceLinked (first :: second :: rest)) :
    TraceLinked (second :: rest) := by
  cases linked with
  | cons _ tailLinked => exact tailLinked

end TraceLinked

/--
生成 trace 是有限的 `List InfoGenStep`，每个元素自身携带 witness，
并且列表上的相邻读出按 `TraceLinked` 链接。
-/
structure GenerationTrace {Source Readout : Type}
    (L : ReadoutSystem Source Readout)
    (Distinguishes : Readout → Source → Source → Prop) where
  steps : List (InfoGenStep L Distinguishes)
  linked : TraceLinked steps

namespace GenerationTrace

theorem info_monotone {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (trace : GenerationTrace L Distinguishes) :
    (step : InfoGenStep L Distinguishes) →
      List.Mem step trace.steps →
        (left right : Source) →
          Distinguishes step.previous left right →
            Distinguishes step.generated left right := by
  intro step _ left right separated
  exact InfoGenStep.info_monotone step left right separated

theorem readback_consistent {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (trace : GenerationTrace L Distinguishes) :
    (step : InfoGenStep L Distinguishes) →
      List.Mem step trace.steps → L.read step.source = step.generated := by
  intro step _
  exact InfoGenStep.readback_consistent step

theorem adjacent_readout {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    {first second : InfoGenStep L Distinguishes}
    {rest : List (InfoGenStep L Distinguishes)}
    (trace : GenerationTrace L Distinguishes)
    (shape : trace.steps = first :: second :: rest) :
    first.generated = second.previous := by
  have linkedShape : TraceLinked (first :: second :: rest) := by
    rw [← shape]
    exact trace.linked
  exact TraceLinked.adjacent linkedShape

end GenerationTrace

/-- 顶层别名：单步信息生成不降低任何已给出的可分辨源对。 -/
theorem info_monotone {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (step : InfoGenStep L Distinguishes) :
    (left right : Source) →
      Distinguishes step.previous left right →
        Distinguishes step.generated left right :=
  InfoGenStep.info_monotone step

/-- 顶层别名：生成读出由 witness 回读到产生它的源对象。 -/
theorem readback_consistent {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (step : InfoGenStep L Distinguishes) :
    L.read step.source = step.generated :=
  InfoGenStep.readback_consistent step

/-- 顶层别名：有限 trace 中每一步都保持旧的可分辨性。 -/
theorem trace_info_monotone {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (trace : GenerationTrace L Distinguishes) :
    (step : InfoGenStep L Distinguishes) →
      List.Mem step trace.steps →
        (left right : Source) →
          Distinguishes step.previous left right →
            Distinguishes step.generated left right :=
  GenerationTrace.info_monotone trace

/-- 顶层别名：有限 trace 中每个生成读出都可回读到其源对象。 -/
theorem trace_readback_consistent {Source Readout : Type}
    {L : ReadoutSystem Source Readout}
    {Distinguishes : Readout → Source → Source → Prop}
    (trace : GenerationTrace L Distinguishes) :
    (step : InfoGenStep L Distinguishes) →
      List.Mem step trace.steps → L.read step.source = step.generated :=
  GenerationTrace.readback_consistent trace

end BEDC.RealityConstrained
