import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LowerSemicontinuousUp : Type where
  | mk
      (source graph epigraph schedule readback comparison transport replay provenance name :
        BHist) : LowerSemicontinuousUp
  deriving DecidableEq

def lowerSemicontinuousEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lowerSemicontinuousEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lowerSemicontinuousEncodeBHist h

def lowerSemicontinuousDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lowerSemicontinuousDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lowerSemicontinuousDecodeBHist tail)

private theorem lowerSemicontinuousDecode_encode_bhist :
    ∀ h : BHist, lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lowerSemicontinuousToEventFlow : LowerSemicontinuousUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LowerSemicontinuousUp.mk source graph epigraph schedule readback comparison transport replay
      provenance name =>
      [[BMark.b0],
        lowerSemicontinuousEncodeBHist source,
        [BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist graph,
        [BMark.b1, BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist epigraph,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist comparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        lowerSemicontinuousEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        lowerSemicontinuousEncodeBHist name]

private def lowerSemicontinuousEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lowerSemicontinuousEventAtDefault index rest

def lowerSemicontinuousFromEventFlow (ef : EventFlow) : Option LowerSemicontinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LowerSemicontinuousUp.mk
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 1 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 3 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 5 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 7 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 9 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 11 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 13 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 15 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 17 ef))
      (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEventAtDefault 19 ef)))

private theorem lowerSemicontinuous_round_trip :
    ∀ x : LowerSemicontinuousUp,
      lowerSemicontinuousFromEventFlow (lowerSemicontinuousToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source graph epigraph schedule readback comparison transport replay provenance name =>
      change
        some
          (LowerSemicontinuousUp.mk
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist source))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist graph))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist epigraph))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist schedule))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist readback))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist comparison))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist transport))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist replay))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist provenance))
            (lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist name))) =
          some
            (LowerSemicontinuousUp.mk source graph epigraph schedule readback comparison transport
              replay provenance name)
      rw [lowerSemicontinuousDecode_encode_bhist source,
        lowerSemicontinuousDecode_encode_bhist graph,
        lowerSemicontinuousDecode_encode_bhist epigraph,
        lowerSemicontinuousDecode_encode_bhist schedule,
        lowerSemicontinuousDecode_encode_bhist readback,
        lowerSemicontinuousDecode_encode_bhist comparison,
        lowerSemicontinuousDecode_encode_bhist transport,
        lowerSemicontinuousDecode_encode_bhist replay,
        lowerSemicontinuousDecode_encode_bhist provenance,
        lowerSemicontinuousDecode_encode_bhist name]

private theorem lowerSemicontinuousToEventFlow_injective {x y : LowerSemicontinuousUp} :
    lowerSemicontinuousToEventFlow x = lowerSemicontinuousToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lowerSemicontinuousFromEventFlow (lowerSemicontinuousToEventFlow x) =
        lowerSemicontinuousFromEventFlow (lowerSemicontinuousToEventFlow y) :=
    congrArg lowerSemicontinuousFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lowerSemicontinuous_round_trip x).symm
      (Eq.trans hread (lowerSemicontinuous_round_trip y)))

instance lowerSemicontinuousBHistCarrier : BHistCarrier LowerSemicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lowerSemicontinuousToEventFlow
  fromEventFlow := lowerSemicontinuousFromEventFlow

instance lowerSemicontinuousChapterTasteGate : ChapterTasteGate LowerSemicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lowerSemicontinuousFromEventFlow (lowerSemicontinuousToEventFlow x) = some x
    exact lowerSemicontinuous_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lowerSemicontinuousToEventFlow_injective heq)

instance lowerSemicontinuousFieldFaithful : FieldFaithful LowerSemicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LowerSemicontinuousUp.mk source graph epigraph schedule readback comparison transport replay
        provenance name =>
        [source, graph, epigraph, schedule, readback, comparison, transport, replay, provenance,
          name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk source₁ graph₁ epigraph₁ schedule₁ readback₁ comparison₁ transport₁ replay₁
        provenance₁ name₁ =>
        cases y with
        | mk source₂ graph₂ epigraph₂ schedule₂ readback₂ comparison₂ transport₂ replay₂
            provenance₂ name₂ =>
            injection h with hSource rest₁
            injection rest₁ with hGraph rest₂
            injection rest₂ with hEpigraph rest₃
            injection rest₃ with hSchedule rest₄
            injection rest₄ with hReadback rest₅
            injection rest₅ with hComparison rest₆
            injection rest₆ with hTransport rest₇
            injection rest₇ with hReplay rest₈
            injection rest₈ with hProvenance rest₉
            injection rest₉ with hName _
            cases hSource
            cases hGraph
            cases hEpigraph
            cases hSchedule
            cases hReadback
            cases hComparison
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

instance lowerSemicontinuousNontrivial : Nontrivial LowerSemicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LowerSemicontinuousUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LowerSemicontinuousUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hSource _ _ _ _ _ _ _ _ _
        cases hSource⟩

theorem LowerSemicontinuousTasteGate_single_carrier_alignment :
    (∀ h : BHist, lowerSemicontinuousDecodeBHist (lowerSemicontinuousEncodeBHist h) = h) ∧
      (∀ x : LowerSemicontinuousUp,
        lowerSemicontinuousFromEventFlow (lowerSemicontinuousToEventFlow x) = some x) ∧
        (∀ x y : LowerSemicontinuousUp,
          lowerSemicontinuousToEventFlow x = lowerSemicontinuousToEventFlow y → x = y) ∧
          lowerSemicontinuousEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact lowerSemicontinuousDecode_encode_bhist
  · constructor
    · exact lowerSemicontinuous_round_trip
    · constructor
      · intro x y heq
        exact lowerSemicontinuousToEventFlow_injective heq
      · rfl

end BEDC.Derived.LowerSemicontinuousUp
