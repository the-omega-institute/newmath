import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICOpenProblemLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICOpenProblemLedgerUp : Type where
  | mk (S C N U D E B H R P Q : BHist) : MetaCICOpenProblemLedgerUp
  deriving DecidableEq

def metaCICOpenProblemLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICOpenProblemLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICOpenProblemLedgerEncodeBHist h

def metaCICOpenProblemLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICOpenProblemLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICOpenProblemLedgerDecodeBHist tail)

private theorem MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fields :
    MetaCICOpenProblemLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICOpenProblemLedgerUp.mk S C N U D E B H R P Q => [S, C, N, U, D, E, B, H, R, P, Q]

def MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow :
    MetaCICOpenProblemLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fields x).map
        metaCICOpenProblemLedgerEncodeBHist

private def MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault index rest

def MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MetaCICOpenProblemLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetaCICOpenProblemLedgerUp.mk
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (metaCICOpenProblemLedgerDecodeBHist
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

private theorem MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICOpenProblemLedgerUp) :
    MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fromEventFlow
      (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S C N U D E B H R P Q =>
      change
        some
          (MetaCICOpenProblemLedgerUp.mk
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist S))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist C))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist N))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist U))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist D))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist E))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist B))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist H))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist R))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist P))
            (metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist Q))) =
          some (MetaCICOpenProblemLedgerUp.mk S C N U D E B H R P Q)
      rw [MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode S,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode C,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode N,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode U,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode D,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode E,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode B,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode H,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode R,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode P,
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode Q]

private theorem MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICOpenProblemLedgerUp} :
    MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow x =
      MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fromEventFlow
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow x) =
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fromEventFlow
          (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MetaCICOpenProblemLedgerUp,
      MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fields x =
        MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ C₁ N₁ U₁ D₁ E₁ B₁ H₁ R₁ P₁ Q₁ =>
      cases y with
      | mk S₂ C₂ N₂ U₂ D₂ E₂ B₂ H₂ R₂ P₂ Q₂ =>
          cases hfields
          rfl

instance metaCICOpenProblemLedgerBHistCarrier :
    BHistCarrier MetaCICOpenProblemLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fromEventFlow

instance metaCICOpenProblemLedgerChapterTasteGate :
    ChapterTasteGate MetaCICOpenProblemLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fromEventFlow
        (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metaCICOpenProblemLedgerFieldFaithful :
    FieldFaithful MetaCICOpenProblemLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fields
  field_faithful := MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_fields_faithful

theorem MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metaCICOpenProblemLedgerDecodeBHist (metaCICOpenProblemLedgerEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetaCICOpenProblemLedgerUp) ∧
        Nonempty (ChapterTasteGate MetaCICOpenProblemLedgerUp) ∧
          metaCICOpenProblemLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetaCICOpenProblemLedgerTasteGate_single_carrier_alignment_decode_encode,
      ⟨metaCICOpenProblemLedgerBHistCarrier⟩,
      ⟨metaCICOpenProblemLedgerChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetaCICOpenProblemLedgerUp
