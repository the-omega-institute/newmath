import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScottContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScottContinuousUp : Type where
  | mk :
      (source target graph directedSuprema scottOpen transport replay provenance localCert :
        BHist) →
      ScottContinuousUp
  deriving DecidableEq

def scottContinuousEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: scottContinuousEncodeBHist h
  | BHist.e1 h => BMark.b1 :: scottContinuousEncodeBHist h

def scottContinuousDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (scottContinuousDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (scottContinuousDecodeBHist tail)

theorem ScottContinuousTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, scottContinuousDecodeBHist (scottContinuousEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def scottContinuousFields : ScottContinuousUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScottContinuousUp.mk source target graph directedSuprema scottOpen transport replay
      provenance localCert =>
      [source, target, graph, directedSuprema, scottOpen, transport, replay, provenance,
        localCert]

def scottContinuousToEventFlow : ScottContinuousUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map scottContinuousEncodeBHist (scottContinuousFields x)

private def ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault index rest

def scottContinuousFromEventFlow : EventFlow → Option ScottContinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ScottContinuousUp.mk
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (scottContinuousDecodeBHist
          (ScottContinuousTasteGate_single_carrier_alignment_eventAtDefault 8 ef)))

theorem ScottContinuousTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ScottContinuousUp,
      scottContinuousFromEventFlow (scottContinuousToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target graph directedSuprema scottOpen transport replay provenance localCert =>
      change
        some
          (ScottContinuousUp.mk
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist source))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist target))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist graph))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist directedSuprema))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist scottOpen))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist transport))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist replay))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist provenance))
            (scottContinuousDecodeBHist (scottContinuousEncodeBHist localCert))) =
          some
            (ScottContinuousUp.mk source target graph directedSuprema scottOpen transport replay
              provenance localCert)
      rw [ScottContinuousTasteGate_single_carrier_alignment_decode_encode source,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode target,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode graph,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode directedSuprema,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode scottOpen,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode transport,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode replay,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode provenance,
        ScottContinuousTasteGate_single_carrier_alignment_decode_encode localCert]

theorem ScottContinuousTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ScottContinuousUp} :
    scottContinuousToEventFlow x = scottContinuousToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      scottContinuousFromEventFlow (scottContinuousToEventFlow x) =
        scottContinuousFromEventFlow (scottContinuousToEventFlow y) :=
    congrArg scottContinuousFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ScottContinuousTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ScottContinuousTasteGate_single_carrier_alignment_round_trip y)))

private theorem scottContinuous_field_faithful :
    ∀ x y : ScottContinuousUp, scottContinuousFields x = scottContinuousFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ target₁ graph₁ directedSuprema₁ scottOpen₁ transport₁ replay₁ provenance₁
      localCert₁ =>
      cases y with
      | mk source₂ target₂ graph₂ directedSuprema₂ scottOpen₂ transport₂ replay₂ provenance₂
          localCert₂ =>
          cases h
          rfl

instance scottContinuousBHistCarrier : BHistCarrier ScottContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := scottContinuousToEventFlow
  fromEventFlow := scottContinuousFromEventFlow

instance scottContinuousChapterTasteGate : ChapterTasteGate ScottContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change scottContinuousFromEventFlow (scottContinuousToEventFlow x) = some x
    exact ScottContinuousTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ScottContinuousTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance scottContinuousFieldFaithful : FieldFaithful ScottContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := scottContinuousFields
  field_faithful := scottContinuous_field_faithful

instance scottContinuousNontrivial : Nontrivial ScottContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ScottContinuousUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ScottContinuousUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ScottContinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  scottContinuousChapterTasteGate

theorem ScottContinuousTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ScottContinuousUp) ∧
      Nonempty (FieldFaithful ScottContinuousUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ScottContinuousUp) ∧
      (∀ h : BHist, scottContinuousDecodeBHist (scottContinuousEncodeBHist h) = h) ∧
      (∀ x : ScottContinuousUp,
        scottContinuousFromEventFlow (scottContinuousToEventFlow x) = some x) ∧
      (∀ x y : ScottContinuousUp,
        scottContinuousToEventFlow x = scottContinuousToEventFlow y → x = y) ∧
      scottContinuousEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro scottContinuousChapterTasteGate
  · constructor
    · exact Nonempty.intro scottContinuousFieldFaithful
    · constructor
      · exact Nonempty.intro scottContinuousNontrivial
      · constructor
        · exact ScottContinuousTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact ScottContinuousTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact ScottContinuousTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.ScottContinuousUp
