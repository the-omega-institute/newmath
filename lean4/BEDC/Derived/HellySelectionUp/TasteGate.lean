import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HellySelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HellySelectionUp : Type where
  | mk (B A W S R E T C P N : BHist) : HellySelectionUp
  deriving DecidableEq

def hellySelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hellySelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hellySelectionEncodeBHist h

def hellySelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hellySelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hellySelectionDecodeBHist tail)

private theorem HellySelectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hellySelectionDecodeBHist (hellySelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hellySelectionFields : HellySelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HellySelectionUp.mk B A W S R E T C P N => [B, A, W, S, R, E, T, C, P, N]

def hellySelectionToEventFlow : HellySelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map hellySelectionEncodeBHist (hellySelectionFields x)

private def hellySelectionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => hellySelectionRawAt n rest

private def hellySelectionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => hellySelectionLengthEq n rest

def hellySelectionFromEventFlow : EventFlow → Option HellySelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match hellySelectionLengthEq 10 flow with
      | true =>
          some
            (HellySelectionUp.mk
              (hellySelectionDecodeBHist (hellySelectionRawAt 0 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 1 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 2 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 3 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 4 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 5 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 6 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 7 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 8 flow))
              (hellySelectionDecodeBHist (hellySelectionRawAt 9 flow)))
      | false => none

private theorem HellySelectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HellySelectionUp,
      hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A W S R E T C P N =>
      change
        some
            (HellySelectionUp.mk
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist B))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist A))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist W))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist S))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist R))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist E))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist T))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist C))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist P))
              (hellySelectionDecodeBHist (hellySelectionEncodeBHist N))) =
          some (HellySelectionUp.mk B A W S R E T C P N)
      rw [HellySelectionTasteGate_single_carrier_alignment_decode B,
        HellySelectionTasteGate_single_carrier_alignment_decode A,
        HellySelectionTasteGate_single_carrier_alignment_decode W,
        HellySelectionTasteGate_single_carrier_alignment_decode S,
        HellySelectionTasteGate_single_carrier_alignment_decode R,
        HellySelectionTasteGate_single_carrier_alignment_decode E,
        HellySelectionTasteGate_single_carrier_alignment_decode T,
        HellySelectionTasteGate_single_carrier_alignment_decode C,
        HellySelectionTasteGate_single_carrier_alignment_decode P,
        HellySelectionTasteGate_single_carrier_alignment_decode N]

private theorem HellySelectionTasteGate_single_carrier_alignment_injective
    {x y : HellySelectionUp}
    (h : hellySelectionToEventFlow x = hellySelectionToEventFlow y) :
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  have hread :
      hellySelectionFromEventFlow (hellySelectionToEventFlow x) =
        hellySelectionFromEventFlow (hellySelectionToEventFlow y) :=
    congrArg hellySelectionFromEventFlow h
  exact Option.some.inj
    (Eq.trans
      (HellySelectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HellySelectionTasteGate_single_carrier_alignment_round_trip y)))

instance hellySelectionBHistCarrier : BHistCarrier HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hellySelectionToEventFlow
  fromEventFlow := hellySelectionFromEventFlow

instance hellySelectionChapterTasteGate : ChapterTasteGate HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x
    exact HellySelectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HellySelectionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate HellySelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hellySelectionChapterTasteGate

theorem HellySelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, hellySelectionDecodeBHist (hellySelectionEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate HellySelectionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HellySelectionTasteGate_single_carrier_alignment_decode,
      Nonempty.intro hellySelectionChapterTasteGate⟩

end BEDC.Derived.HellySelectionUp
