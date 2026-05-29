import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalContractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalContractionUp : Type where
  | mk (I F L D W R E H C P N : BHist) : BishopIntervalContractionUp
  deriving DecidableEq

def bishopIntervalContractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalContractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalContractionEncodeBHist h

def bishopIntervalContractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalContractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalContractionDecodeBHist tail)

private theorem BishopIntervalContractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopIntervalContractionFields : BishopIntervalContractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalContractionUp.mk I F L D W R E H C P N =>
      [I, F, L, D, W, R, E, H, C, P, N]

def bishopIntervalContractionToEventFlow : BishopIntervalContractionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopIntervalContractionFields x).map bishopIntervalContractionEncodeBHist

private def bishopIntervalContractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopIntervalContractionEventAtDefault index rest

def bishopIntervalContractionFromEventFlow
    (ef : EventFlow) : Option BishopIntervalContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopIntervalContractionUp.mk
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 0 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 1 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 2 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 3 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 4 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 5 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 6 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 7 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 8 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 9 ef))
      (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEventAtDefault 10 ef)))

private theorem BishopIntervalContractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopIntervalContractionUp,
      bishopIntervalContractionFromEventFlow (bishopIntervalContractionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F L D W R E H C P N =>
      change
        some
          (BishopIntervalContractionUp.mk
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist I))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist F))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist L))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist D))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist W))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist R))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist E))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist H))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist C))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist P))
            (bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist N))) =
          some (BishopIntervalContractionUp.mk I F L D W R E H C P N)
      rw [BishopIntervalContractionTasteGate_single_carrier_alignment_decode I,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode F,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode L,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode D,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode W,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode R,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode E,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode H,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode C,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode P,
        BishopIntervalContractionTasteGate_single_carrier_alignment_decode N]

private theorem BishopIntervalContractionTasteGate_single_carrier_alignment_injective
    {x y : BishopIntervalContractionUp} :
    bishopIntervalContractionToEventFlow x = bishopIntervalContractionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalContractionFromEventFlow (bishopIntervalContractionToEventFlow x) =
        bishopIntervalContractionFromEventFlow (bishopIntervalContractionToEventFlow y) :=
    congrArg bishopIntervalContractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopIntervalContractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopIntervalContractionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopIntervalContractionBHistCarrier :
    BHistCarrier BishopIntervalContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalContractionToEventFlow
  fromEventFlow := bishopIntervalContractionFromEventFlow

instance bishopIntervalContractionChapterTasteGate :
    ChapterTasteGate BishopIntervalContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopIntervalContractionFromEventFlow (bishopIntervalContractionToEventFlow x) =
        some x
    exact BishopIntervalContractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopIntervalContractionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate BishopIntervalContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopIntervalContractionChapterTasteGate

theorem BishopIntervalContractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopIntervalContractionDecodeBHist (bishopIntervalContractionEncodeBHist h) = h) ∧
      (∀ x : BishopIntervalContractionUp,
        bishopIntervalContractionFromEventFlow (bishopIntervalContractionToEventFlow x) =
          some x) ∧
        (∀ x y : BishopIntervalContractionUp,
          bishopIntervalContractionToEventFlow x = bishopIntervalContractionToEventFlow y →
            x = y) ∧
          bishopIntervalContractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopIntervalContractionTasteGate_single_carrier_alignment_decode,
      BishopIntervalContractionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => BishopIntervalContractionTasteGate_single_carrier_alignment_injective h),
      rfl⟩

end BEDC.Derived.BishopIntervalContractionUp
