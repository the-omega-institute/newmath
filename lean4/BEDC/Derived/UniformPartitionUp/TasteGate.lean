import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformPartitionUp : Type where
  | mk (interval origin width count cells coverage handoff boundary transport replay
      provenance localName : BHist) : UniformPartitionUp

def uniformPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformPartitionEncodeBHist h

def uniformPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformPartitionDecodeBHist tail)

private theorem uniformPartition_decode_encode_bhist :
    ∀ h : BHist, uniformPartitionDecodeBHist (uniformPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformPartitionFields : UniformPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformPartitionUp.mk interval origin width count cells coverage handoff boundary
      transport replay provenance localName =>
      [interval, origin, width, count, cells, coverage, handoff, boundary, transport,
        replay, provenance, localName]

def uniformPartitionToEventFlow : UniformPartitionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformPartitionFields x).map uniformPartitionEncodeBHist

private def uniformPartitionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformPartitionEventAtDefault index rest

def uniformPartitionFromEventFlow (flow : EventFlow) : Option UniformPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformPartitionUp.mk
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 0 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 1 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 2 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 3 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 4 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 5 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 6 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 7 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 8 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 9 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 10 flow))
      (uniformPartitionDecodeBHist (uniformPartitionEventAtDefault 11 flow)))

private theorem uniformPartition_round_trip :
    ∀ x : UniformPartitionUp,
      uniformPartitionFromEventFlow (uniformPartitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval origin width count cells coverage handoff boundary transport replay
      provenance localName =>
      change
        some
          (UniformPartitionUp.mk
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist interval))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist origin))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist width))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist count))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist cells))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist coverage))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist handoff))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist boundary))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist transport))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist replay))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist provenance))
            (uniformPartitionDecodeBHist (uniformPartitionEncodeBHist localName))) =
          some
            (UniformPartitionUp.mk interval origin width count cells coverage handoff
              boundary transport replay provenance localName)
      rw [uniformPartition_decode_encode_bhist interval,
        uniformPartition_decode_encode_bhist origin,
        uniformPartition_decode_encode_bhist width,
        uniformPartition_decode_encode_bhist count,
        uniformPartition_decode_encode_bhist cells,
        uniformPartition_decode_encode_bhist coverage,
        uniformPartition_decode_encode_bhist handoff,
        uniformPartition_decode_encode_bhist boundary,
        uniformPartition_decode_encode_bhist transport,
        uniformPartition_decode_encode_bhist replay,
        uniformPartition_decode_encode_bhist provenance,
        uniformPartition_decode_encode_bhist localName]

private theorem uniformPartitionToEventFlow_injective {x y : UniformPartitionUp} :
    uniformPartitionToEventFlow x = uniformPartitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformPartitionFromEventFlow (uniformPartitionToEventFlow x) =
        uniformPartitionFromEventFlow (uniformPartitionToEventFlow y) :=
    congrArg uniformPartitionFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (uniformPartition_round_trip x).symm
        (Eq.trans hread (uniformPartition_round_trip y)))

private theorem uniformPartition_fields_faithful :
    ∀ x y : UniformPartitionUp, uniformPartitionFields x = uniformPartitionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk interval₁ origin₁ width₁ count₁ cells₁ coverage₁ handoff₁ boundary₁ transport₁
      replay₁ provenance₁ localName₁ =>
      cases y with
      | mk interval₂ origin₂ width₂ count₂ cells₂ coverage₂ handoff₂ boundary₂ transport₂
          replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance uniformPartitionBHistCarrier : BHistCarrier UniformPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformPartitionToEventFlow
  fromEventFlow := uniformPartitionFromEventFlow

instance uniformPartitionChapterTasteGate :
    ChapterTasteGate UniformPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformPartitionFromEventFlow (uniformPartitionToEventFlow x) = some x
    exact uniformPartition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformPartitionToEventFlow_injective heq)

instance uniformPartitionFieldFaithful : FieldFaithful UniformPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformPartitionFields
  field_faithful := uniformPartition_fields_faithful

instance uniformPartitionNontrivial : Nontrivial UniformPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      UniformPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformPartitionChapterTasteGate

def taste_gate_witness : FieldFaithful UniformPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformPartitionFieldFaithful

theorem UniformPartitionTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformPartitionDecodeBHist (uniformPartitionEncodeBHist h) = h) ∧
      (∀ x : UniformPartitionUp,
        uniformPartitionFromEventFlow (uniformPartitionToEventFlow x) = some x) ∧
        (∀ x y : UniformPartitionUp,
          uniformPartitionToEventFlow x = uniformPartitionToEventFlow y → x = y) ∧
          uniformPartitionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨uniformPartition_decode_encode_bhist,
      uniformPartition_round_trip,
      (fun _ _ heq => uniformPartitionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformPartitionUp
