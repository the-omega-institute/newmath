import BEDC.Derived.RealityConstrained.LayeredNormalForms
import BEDC.Derived.RealityConstrained.ConstructiveInfoGen
import BEDC.Derived.RationalUp.Core

namespace BEDC.RealityConstrained

abbrev RationalWeight := BEDC.Derived.RationalUp.RatNum

def rationalWeightZero : RationalWeight :=
  BEDC.Derived.RationalUp.ratZero

def rationalWeightOne : RationalWeight :=
  BEDC.Derived.RationalUp.ratOne

def rationalWeightAdd (left right : RationalWeight) : RationalWeight :=
  BEDC.Derived.RationalUp.ratAdd left right

def RationalWeightEq (left right : RationalWeight) : Prop :=
  BEDC.Derived.RationalUp.RatEq left right

/--
有限测量基只记录可公开列出的结果面。这里的可区分性只是
结果列表上的结构关系，不加入物理动力学语义。
-/
structure MeasurementBasis (Outcome : Type) where
  outcomes : List Outcome
  inhabited_outcome : ∃ outcome : Outcome, List.Mem outcome outcomes
  distinguishable : Outcome → Outcome → Prop
  listed_pair_separates :
    (left right : Outcome) →
      List.Mem left outcomes →
        List.Mem right outcomes →
          left = right ∨ distinguishable left right
  distinguishable_left_listed :
    (left right : Outcome) → distinguishable left right → List.Mem left outcomes
  distinguishable_right_listed :
    (left right : Outcome) → distinguishable left right → List.Mem right outcomes

namespace MeasurementBasis

def Listed {Outcome : Type} (basis : MeasurementBasis Outcome) (outcome : Outcome) :
    Prop :=
  List.Mem outcome basis.outcomes

theorem occupied {Outcome : Type} (basis : MeasurementBasis Outcome) :
    ∃ outcome : Outcome, basis.Listed outcome :=
  basis.inhabited_outcome

theorem listed_pair_separation {Outcome : Type} (basis : MeasurementBasis Outcome)
    {left right : Outcome}
    (leftMem : basis.Listed left) (rightMem : basis.Listed right) :
    left = right ∨ basis.distinguishable left right :=
  basis.listed_pair_separates left right leftMem rightMem

theorem distinguishable_left_mem {Outcome : Type} (basis : MeasurementBasis Outcome)
    {left right : Outcome}
    (apart : basis.distinguishable left right) :
    basis.Listed left :=
  basis.distinguishable_left_listed left right apart

theorem distinguishable_right_mem {Outcome : Type} (basis : MeasurementBasis Outcome)
    {left right : Outcome}
    (apart : basis.distinguishable left right) :
    basis.Listed right :=
  basis.distinguishable_right_listed left right apart

end MeasurementBasis

structure OutcomeWeight (Outcome : Type) where
  outcome : Outcome
  weight : RationalWeight

abbrev MeasurementDistribution (Outcome : Type) :=
  List (OutcomeWeight Outcome)

def measurementWeightSum {Outcome : Type} : MeasurementDistribution Outcome → RationalWeight
  | [] => rationalWeightZero
  | entry :: rest => rationalWeightAdd entry.weight (measurementWeightSum rest)

/--
测量 channel 从源对象给出一个有限结果分布。权重是 BEDC 已有
有理数载体，归一化只声明有限权重和等于一。
-/
structure MeasurementChannel (Source Outcome : Type)
    (basis : MeasurementBasis Outcome) where
  distribution : Source → MeasurementDistribution Outcome
  support_in_basis :
    (source : Source) →
      (entry : OutcomeWeight Outcome) →
        List.Mem entry (distribution source) →
          basis.Listed entry.outcome
  born_like_normalization :
    (source : Source) →
      RationalWeightEq (measurementWeightSum (distribution source)) rationalWeightOne

namespace MeasurementChannel

theorem listed_support {Source Outcome : Type}
    {basis : MeasurementBasis Outcome}
    (channel : MeasurementChannel Source Outcome basis)
    (source : Source) (entry : OutcomeWeight Outcome)
    (member : List.Mem entry (channel.distribution source)) :
    basis.Listed entry.outcome :=
  channel.support_in_basis source entry member

theorem normalized {Source Outcome : Type}
    {basis : MeasurementBasis Outcome}
    (channel : MeasurementChannel Source Outcome basis)
    (source : Source) :
    RationalWeightEq (measurementWeightSum (channel.distribution source))
      rationalWeightOne :=
  channel.born_like_normalization source

end MeasurementChannel

/--
有限测量接口把有限结果分布接到一个 `ReadoutSystem`。每个出现在
source 分布中的结果必须回读到同一 source 的公开投影。
-/
structure MeasurementInterface (Source Outcome Projection : Type) where
  basis : MeasurementBasis Outcome
  readout_system : ReadoutSystem Source Projection
  channel : MeasurementChannel Source Outcome basis
  result_projection : Outcome → Projection
  readback :
    (source : Source) →
      (entry : OutcomeWeight Outcome) →
        List.Mem entry (channel.distribution source) →
          readout_system.read source = result_projection entry.outcome

namespace MeasurementInterface

theorem support_in_basis {Source Outcome Projection : Type}
    (interface : MeasurementInterface Source Outcome Projection)
    (source : Source) (entry : OutcomeWeight Outcome)
    (member : List.Mem entry (interface.channel.distribution source)) :
    interface.basis.Listed entry.outcome :=
  interface.channel.support_in_basis source entry member

theorem born_like_normalization {Source Outcome Projection : Type}
    (interface : MeasurementInterface Source Outcome Projection)
    (source : Source) :
    RationalWeightEq (measurementWeightSum (interface.channel.distribution source))
      rationalWeightOne :=
  interface.channel.born_like_normalization source

theorem readback_projection {Source Outcome Projection : Type}
    (interface : MeasurementInterface Source Outcome Projection)
    (source : Source) (entry : OutcomeWeight Outcome)
    (member : List.Mem entry (interface.channel.distribution source)) :
    interface.readout_system.read source = interface.result_projection entry.outcome :=
  interface.readback source entry member

theorem readback_entry_listed_and_projected {Source Outcome Projection : Type}
    (interface : MeasurementInterface Source Outcome Projection)
    (source : Source) (entry : OutcomeWeight Outcome)
    (member : List.Mem entry (interface.channel.distribution source)) :
    interface.basis.Listed entry.outcome ∧
      interface.readout_system.read source = interface.result_projection entry.outcome :=
  And.intro
    (interface.support_in_basis source entry member)
    (interface.readback_projection source entry member)

theorem realized_readout_system_readback {Source Outcome Projection : Type}
    (interface : MeasurementInterface Source Outcome Projection)
    (outcome : Outcome)
    (fiber : interface.readout_system.Fiber (interface.result_projection outcome)) :
    interface.readout_system.read
        (interface.readout_system.realize (interface.result_projection outcome) fiber) =
      interface.result_projection outcome :=
  interface.readout_system.read_realize (interface.result_projection outcome) fiber

end MeasurementInterface

/--
测量生成 witness 是已有信息生成 witness 在有限测量结果投影上的实例。
它只把结果投影接入 `InfoGenWitness`，不提供物理 Born 规则。
-/
structure MeasurementGenerationWitness {Source Outcome Projection : Type}
    (interface : MeasurementInterface Source Outcome Projection)
    (Distinguishes : Projection → Source → Source → Prop)
    (source : Source) (previous : Projection)
    (entry : OutcomeWeight Outcome)
    (member : List.Mem entry (interface.channel.distribution source)) where
  witness :
    InfoGenWitness interface.readout_system Distinguishes source previous
      (interface.result_projection entry.outcome)

namespace MeasurementGenerationWitness

theorem generated_projection_readback {Source Outcome Projection : Type}
    {interface : MeasurementInterface Source Outcome Projection}
    {Distinguishes : Projection → Source → Source → Prop}
    {source : Source} {previous : Projection}
    {entry : OutcomeWeight Outcome}
    {member : List.Mem entry (interface.channel.distribution source)}
    (witness : MeasurementGenerationWitness interface Distinguishes source previous
      entry member) :
    interface.readout_system.read source = interface.result_projection entry.outcome :=
  InfoGenWitness.readback_consistent witness.witness

theorem generated_distinction {Source Outcome Projection : Type}
    {interface : MeasurementInterface Source Outcome Projection}
    {Distinguishes : Projection → Source → Source → Prop}
    {source : Source} {previous : Projection}
    {entry : OutcomeWeight Outcome}
    {member : List.Mem entry (interface.channel.distribution source)}
    (witness : MeasurementGenerationWitness interface Distinguishes source previous
      entry member) :
    Distinguishes (interface.result_projection entry.outcome) source
        witness.witness.comparison ∧
      (Distinguishes previous source witness.witness.comparison → False) :=
  InfoGenWitness.new_distinction witness.witness

end MeasurementGenerationWitness

end BEDC.RealityConstrained
