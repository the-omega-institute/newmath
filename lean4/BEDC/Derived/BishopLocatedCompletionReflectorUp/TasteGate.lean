import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCompletionReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCompletionReflectorUp : Type where
  | mk (B R D S Q L E H C P N : BHist) : BishopLocatedCompletionReflectorUp
  deriving DecidableEq

def bishopLocatedCompletionReflectorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCompletionReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCompletionReflectorEncodeBHist h

def bishopLocatedCompletionReflectorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCompletionReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCompletionReflectorDecodeBHist tail)

private theorem BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCompletionReflectorFields :
    BishopLocatedCompletionReflectorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCompletionReflectorUp.mk B R D S Q L E H C P N =>
      [B, R, D, S, Q, L, E, H, C, P, N]

def bishopLocatedCompletionReflectorToEventFlow :
    BishopLocatedCompletionReflectorUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopLocatedCompletionReflectorFields x).map
      bishopLocatedCompletionReflectorEncodeBHist

private def bishopLocatedCompletionReflectorEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopLocatedCompletionReflectorEventAtDefault index rest

def bishopLocatedCompletionReflectorFromEventFlow
    (ef : EventFlow) : Option BishopLocatedCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedCompletionReflectorUp.mk
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 0 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 1 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 2 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 3 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 4 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 5 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 6 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 7 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 8 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 9 ef))
      (bishopLocatedCompletionReflectorDecodeBHist
        (bishopLocatedCompletionReflectorEventAtDefault 10 ef)))

private theorem BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip :
    forall x : BishopLocatedCompletionReflectorUp,
      bishopLocatedCompletionReflectorFromEventFlow
        (bishopLocatedCompletionReflectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B R D S Q L E H C P N =>
      change
        some
          (BishopLocatedCompletionReflectorUp.mk
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist B))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist R))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist D))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist S))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist Q))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist L))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist E))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist H))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist C))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist P))
            (bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist N))) =
          some (BishopLocatedCompletionReflectorUp.mk B R D S Q L E H C P N)
      rw [BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode B,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode R,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode D,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode S,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode Q,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode L,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode E,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode H,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode C,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode P,
        BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedCompletionReflectorUp} :
    bishopLocatedCompletionReflectorToEventFlow x =
      bishopLocatedCompletionReflectorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCompletionReflectorFromEventFlow
          (bishopLocatedCompletionReflectorToEventFlow x) =
        bishopLocatedCompletionReflectorFromEventFlow
          (bishopLocatedCompletionReflectorToEventFlow y) :=
    congrArg bishopLocatedCompletionReflectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_fields :
    forall x y : BishopLocatedCompletionReflectorUp,
      bishopLocatedCompletionReflectorFields x =
        bishopLocatedCompletionReflectorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 R1 D1 S1 Q1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 R2 D2 S2 Q2 L2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedCompletionReflectorBHistCarrier :
    BHistCarrier BishopLocatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCompletionReflectorToEventFlow
  fromEventFlow := bishopLocatedCompletionReflectorFromEventFlow

instance bishopLocatedCompletionReflectorChapterTasteGate :
    ChapterTasteGate BishopLocatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedCompletionReflectorFromEventFlow
        (bishopLocatedCompletionReflectorToEventFlow x) = some x
    exact BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance bishopLocatedCompletionReflectorFieldFaithful :
    FieldFaithful BishopLocatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedCompletionReflectorFields
  field_faithful :=
    BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_fields

instance bishopLocatedCompletionReflectorNontrivial :
    Nontrivial BishopLocatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedCompletionReflectorUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BishopLocatedCompletionReflectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCompletionReflectorChapterTasteGate

theorem BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopLocatedCompletionReflectorUp) ∧
      Nonempty (FieldFaithful BishopLocatedCompletionReflectorUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopLocatedCompletionReflectorUp) ∧
          (forall h : BHist,
            bishopLocatedCompletionReflectorDecodeBHist
              (bishopLocatedCompletionReflectorEncodeBHist h) = h) ∧
            (forall x : BishopLocatedCompletionReflectorUp,
              bishopLocatedCompletionReflectorFromEventFlow
                (bishopLocatedCompletionReflectorToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨bishopLocatedCompletionReflectorChapterTasteGate⟩,
      ⟨bishopLocatedCompletionReflectorFieldFaithful⟩,
      ⟨bishopLocatedCompletionReflectorNontrivial⟩,
      BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_decode,
      BishopLocatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.BishopLocatedCompletionReflectorUp
