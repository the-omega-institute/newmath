import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LebesgueNumberFiniteCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LebesgueNumberFiniteCoverUp : Type where
  | mk (source cover radius refinement exactness transport replay provenance localName : BHist) :
      LebesgueNumberFiniteCoverUp
  deriving DecidableEq

def lebesgueNumberFiniteCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lebesgueNumberFiniteCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lebesgueNumberFiniteCoverEncodeBHist h

def lebesgueNumberFiniteCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lebesgueNumberFiniteCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lebesgueNumberFiniteCoverDecodeBHist tail)

private theorem LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lebesgueNumberFiniteCoverFields : LebesgueNumberFiniteCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LebesgueNumberFiniteCoverUp.mk source cover radius refinement exactness transport replay
      provenance localName =>
      [source, cover, radius, refinement, exactness, transport, replay, provenance, localName]

def lebesgueNumberFiniteCoverToEventFlow : LebesgueNumberFiniteCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lebesgueNumberFiniteCoverFields x).map lebesgueNumberFiniteCoverEncodeBHist

private def lebesgueNumberFiniteCoverEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lebesgueNumberFiniteCoverEventAt index rest

def lebesgueNumberFiniteCoverFromEventFlow (ef : EventFlow) :
    Option LebesgueNumberFiniteCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LebesgueNumberFiniteCoverUp.mk
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 0 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 1 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 2 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 3 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 4 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 5 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 6 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 7 ef))
      (lebesgueNumberFiniteCoverDecodeBHist (lebesgueNumberFiniteCoverEventAt 8 ef)))

private theorem LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_round_trip
    (x : LebesgueNumberFiniteCoverUp) :
    lebesgueNumberFiniteCoverFromEventFlow (lebesgueNumberFiniteCoverToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source cover radius refinement exactness transport replay provenance localName =>
      change
        some
          (LebesgueNumberFiniteCoverUp.mk
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist source))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist cover))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist radius))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist refinement))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist exactness))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist transport))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist replay))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist provenance))
            (lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist localName))) =
          some
            (LebesgueNumberFiniteCoverUp.mk source cover radius refinement exactness transport
              replay provenance localName)
      rw [LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode source,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode cover,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode radius,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode refinement,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode exactness,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode transport,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode replay,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode provenance,
        LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode localName]

private theorem LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LebesgueNumberFiniteCoverUp} :
    lebesgueNumberFiniteCoverToEventFlow x = lebesgueNumberFiniteCoverToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lebesgueNumberFiniteCoverFromEventFlow (lebesgueNumberFiniteCoverToEventFlow x) =
        lebesgueNumberFiniteCoverFromEventFlow (lebesgueNumberFiniteCoverToEventFlow y) :=
    congrArg lebesgueNumberFiniteCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_round_trip y)))

private theorem LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : LebesgueNumberFiniteCoverUp,
      lebesgueNumberFiniteCoverFields x = lebesgueNumberFiniteCoverFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ cover₁ radius₁ refinement₁ exactness₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk source₂ cover₂ radius₂ refinement₂ exactness₂ transport₂ replay₂ provenance₂
          localName₂ =>
          cases hfields
          rfl

instance lebesgueNumberFiniteCoverBHistCarrier :
    BHistCarrier LebesgueNumberFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lebesgueNumberFiniteCoverToEventFlow
  fromEventFlow := lebesgueNumberFiniteCoverFromEventFlow

instance lebesgueNumberFiniteCoverChapterTasteGate :
    ChapterTasteGate LebesgueNumberFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lebesgueNumberFiniteCoverFromEventFlow
      (lebesgueNumberFiniteCoverToEventFlow x) = some x
    exact LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lebesgueNumberFiniteCoverFieldFaithful :
    FieldFaithful LebesgueNumberFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lebesgueNumberFiniteCoverFields
  field_faithful :=
    LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_field_faithful

instance lebesgueNumberFiniteCoverNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LebesgueNumberFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LebesgueNumberFiniteCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LebesgueNumberFiniteCoverUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LebesgueNumberFiniteCoverUp) ∧
      Nonempty (FieldFaithful LebesgueNumberFiniteCoverUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LebesgueNumberFiniteCoverUp) ∧
          (∀ h : BHist,
            lebesgueNumberFiniteCoverDecodeBHist
              (lebesgueNumberFiniteCoverEncodeBHist h) = h) ∧
            (∀ x : LebesgueNumberFiniteCoverUp,
              lebesgueNumberFiniteCoverFromEventFlow
                (lebesgueNumberFiniteCoverToEventFlow x) = some x) ∧
              lebesgueNumberFiniteCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨lebesgueNumberFiniteCoverChapterTasteGate⟩,
      ⟨lebesgueNumberFiniteCoverFieldFaithful⟩, ⟨lebesgueNumberFiniteCoverNontrivial⟩,
      LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_decode_encode,
      LebesgueNumberFiniteCoverTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.LebesgueNumberFiniteCoverUp
