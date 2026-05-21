import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformContinuityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformContinuityUp : Type where
  | mk
      (sourceMetric targetMetric graph tolerance probeBundle center radius coverage lowerBound
        triangle transport nameCert : BHist) :
        UniformContinuityUp
  deriving DecidableEq

def uniformContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformContinuityEncodeBHist h

def uniformContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformContinuityDecodeBHist tail)

private theorem uniformContinuityDecode_encode_bhist :
    ∀ h : BHist, uniformContinuityDecodeBHist (uniformContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def uniformContinuityFields : UniformContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformContinuityUp.mk sourceMetric targetMetric graph tolerance probeBundle center radius
      coverage lowerBound triangle transport nameCert =>
      [sourceMetric, targetMetric, graph, tolerance, probeBundle, center, radius, coverage,
        lowerBound, triangle, transport, nameCert]

def uniformContinuityToEventFlow : UniformContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformContinuityUp.mk sourceMetric targetMetric graph tolerance probeBundle center radius
      coverage lowerBound triangle transport nameCert =>
      [[BMark.b1, BMark.b1, BMark.b0],
        uniformContinuityEncodeBHist sourceMetric,
        uniformContinuityEncodeBHist targetMetric,
        uniformContinuityEncodeBHist graph,
        uniformContinuityEncodeBHist tolerance,
        uniformContinuityEncodeBHist probeBundle,
        uniformContinuityEncodeBHist center,
        uniformContinuityEncodeBHist radius,
        uniformContinuityEncodeBHist coverage,
        uniformContinuityEncodeBHist lowerBound,
        uniformContinuityEncodeBHist triangle,
        uniformContinuityEncodeBHist transport,
        uniformContinuityEncodeBHist nameCert]

private def uniformContinuityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformContinuityEventAt index rest

def uniformContinuityFromEventFlow : EventFlow → Option UniformContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (UniformContinuityUp.mk
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 1 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 2 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 3 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 4 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 5 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 6 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 7 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 8 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 9 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 10 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 11 ef))
          (uniformContinuityDecodeBHist (uniformContinuityEventAt 12 ef)))

private theorem uniformContinuity_round_trip :
    ∀ x : UniformContinuityUp,
      uniformContinuityFromEventFlow (uniformContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceMetric targetMetric graph tolerance probeBundle center radius coverage lowerBound
      triangle transport nameCert =>
      change
        some
          (UniformContinuityUp.mk
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist sourceMetric))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist targetMetric))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist graph))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist tolerance))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist probeBundle))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist center))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist radius))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist coverage))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist lowerBound))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist triangle))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist transport))
            (uniformContinuityDecodeBHist (uniformContinuityEncodeBHist nameCert))) =
          some
            (UniformContinuityUp.mk sourceMetric targetMetric graph tolerance probeBundle center
              radius coverage lowerBound triangle transport nameCert)
      rw [uniformContinuityDecode_encode_bhist sourceMetric,
        uniformContinuityDecode_encode_bhist targetMetric,
        uniformContinuityDecode_encode_bhist graph,
        uniformContinuityDecode_encode_bhist tolerance,
        uniformContinuityDecode_encode_bhist probeBundle,
        uniformContinuityDecode_encode_bhist center,
        uniformContinuityDecode_encode_bhist radius,
        uniformContinuityDecode_encode_bhist coverage,
        uniformContinuityDecode_encode_bhist lowerBound,
        uniformContinuityDecode_encode_bhist triangle,
        uniformContinuityDecode_encode_bhist transport,
        uniformContinuityDecode_encode_bhist nameCert]

private theorem uniformContinuityToEventFlow_injective {x y : UniformContinuityUp} :
    uniformContinuityToEventFlow x = uniformContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformContinuityFromEventFlow (uniformContinuityToEventFlow x) =
        uniformContinuityFromEventFlow (uniformContinuityToEventFlow y) :=
    congrArg uniformContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformContinuity_round_trip x).symm
      (Eq.trans hread (uniformContinuity_round_trip y)))

private theorem uniformContinuity_fields_faithful :
    ∀ x y : UniformContinuityUp,
      uniformContinuityFields x = uniformContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk sourceMetric₁ targetMetric₁ graph₁ tolerance₁ probeBundle₁ center₁ radius₁ coverage₁
      lowerBound₁ triangle₁ transport₁ nameCert₁ =>
      cases y with
      | mk sourceMetric₂ targetMetric₂ graph₂ tolerance₂ probeBundle₂ center₂ radius₂
          coverage₂ lowerBound₂ triangle₂ transport₂ nameCert₂ =>
          injection h with hsourceMetric rest₁
          injection rest₁ with htargetMetric rest₂
          injection rest₂ with hgraph rest₃
          injection rest₃ with htolerance rest₄
          injection rest₄ with hprobeBundle rest₅
          injection rest₅ with hcenter rest₆
          injection rest₆ with hradius rest₇
          injection rest₇ with hcoverage rest₈
          injection rest₈ with hlowerBound rest₉
          injection rest₉ with htriangle rest₁₀
          injection rest₁₀ with htransport rest₁₁
          injection rest₁₁ with hnameCert _
          cases hsourceMetric
          cases htargetMetric
          cases hgraph
          cases htolerance
          cases hprobeBundle
          cases hcenter
          cases hradius
          cases hcoverage
          cases hlowerBound
          cases htriangle
          cases htransport
          cases hnameCert
          rfl

instance uniformContinuityBHistCarrier : BHistCarrier UniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformContinuityToEventFlow
  fromEventFlow := uniformContinuityFromEventFlow

instance uniformContinuityChapterTasteGate : ChapterTasteGate UniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformContinuityFromEventFlow (uniformContinuityToEventFlow x) = some x
    exact uniformContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformContinuityToEventFlow_injective heq)

instance uniformContinuityFieldFaithful : FieldFaithful UniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformContinuityFields
  field_faithful := uniformContinuity_fields_faithful

instance uniformContinuityNontrivial : Nontrivial UniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformContinuityUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformContinuityUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformContinuityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformContinuityUp) ∧
      Nonempty (FieldFaithful UniformContinuityUp) ∧
        Nonempty (Nontrivial UniformContinuityUp) ∧
          (∀ h : BHist,
            uniformContinuityDecodeBHist (uniformContinuityEncodeBHist h) = h) ∧
            (∀ x : UniformContinuityUp,
              uniformContinuityFromEventFlow (uniformContinuityToEventFlow x) = some x) ∧
              (∀ x y : UniformContinuityUp,
                uniformContinuityToEventFlow x = uniformContinuityToEventFlow y → x = y) ∧
                uniformContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro uniformContinuityChapterTasteGate,
      Nonempty.intro uniformContinuityFieldFaithful,
      Nonempty.intro uniformContinuityNontrivial,
      uniformContinuityDecode_encode_bhist,
      uniformContinuity_round_trip,
      by
        intro x y heq
        exact uniformContinuityToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.UniformContinuityUp.TasteGate
