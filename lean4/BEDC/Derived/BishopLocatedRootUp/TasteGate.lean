import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedRootUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedRootUp : Type where
  | mk (B O S D Q E H C P N : BHist) : BishopLocatedRootUp
  deriving DecidableEq

def bishopLocatedRootEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedRootEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedRootEncodeBHist h

def bishopLocatedRootDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedRootDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedRootDecodeBHist tail)

private theorem BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BishopLocatedRootTasteGate_single_carrier_alignment_fields :
    BishopLocatedRootUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedRootUp.mk B O S D Q E H C P N => [B, O, S, D, Q, E, H, C, P, N]

def BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow :
    BishopLocatedRootUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (BishopLocatedRootTasteGate_single_carrier_alignment_fields x).map
      bishopLocatedRootEncodeBHist

private def BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault index rest

def BishopLocatedRootTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BishopLocatedRootUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedRootUp.mk
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (bishopLocatedRootDecodeBHist
        (BishopLocatedRootTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem BishopLocatedRootTasteGate_single_carrier_alignment_round_trip
    (x : BishopLocatedRootUp) :
    BishopLocatedRootTasteGate_single_carrier_alignment_fromEventFlow
        (BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B O S D Q E H C P N =>
      change
        some
          (BishopLocatedRootUp.mk
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist B))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist O))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist S))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist D))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist Q))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist E))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist H))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist C))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist P))
            (bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist N))) =
          some (BishopLocatedRootUp.mk B O S D Q E H C P N)
      rw [BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode B,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode O,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode S,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode D,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode Q,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode E,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode H,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode C,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode P,
        BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedRootUp} :
    BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow x =
        BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BishopLocatedRootTasteGate_single_carrier_alignment_fromEventFlow
          (BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow x) =
        BishopLocatedRootTasteGate_single_carrier_alignment_fromEventFlow
          (BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BishopLocatedRootTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedRootTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopLocatedRootTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedRootTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopLocatedRootUp,
      BishopLocatedRootTasteGate_single_carrier_alignment_fields x =
          BishopLocatedRootTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 O1 S1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 O2 S2 D2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedRootBHistCarrier : BHistCarrier BishopLocatedRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BishopLocatedRootTasteGate_single_carrier_alignment_fromEventFlow

instance bishopLocatedRootChapterTasteGate : ChapterTasteGate BishopLocatedRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BishopLocatedRootTasteGate_single_carrier_alignment_fromEventFlow
          (BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BishopLocatedRootTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedRootTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopLocatedRootFieldFaithful : FieldFaithful BishopLocatedRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BishopLocatedRootTasteGate_single_carrier_alignment_fields
  field_faithful := BishopLocatedRootTasteGate_single_carrier_alignment_fields_faithful

instance bishopLocatedRootNontrivial : Nontrivial BishopLocatedRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedRootUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedRootUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopLocatedRootTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopLocatedRootDecodeBHist (bishopLocatedRootEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopLocatedRootUp) ∧
        Nonempty (ChapterTasteGate BishopLocatedRootUp) ∧
          Nonempty (FieldFaithful BishopLocatedRootUp) ∧
            Nonempty (Nontrivial BishopLocatedRootUp) ∧
              bishopLocatedRootEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopLocatedRootTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨bishopLocatedRootBHistCarrier⟩,
        ⟨⟨bishopLocatedRootChapterTasteGate⟩,
          ⟨⟨bishopLocatedRootFieldFaithful⟩, ⟨⟨bishopLocatedRootNontrivial⟩, rfl⟩⟩⟩⟩⟩

end BEDC.Derived.BishopLocatedRootUp.TasteGate
