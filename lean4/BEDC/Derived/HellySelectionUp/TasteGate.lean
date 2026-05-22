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

private theorem HellySelectionUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hellySelectionDecodeBHist (hellySelectionEncodeBHist h) = h := by
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
  | x => (hellySelectionFields x).map hellySelectionEncodeBHist

private def hellySelectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hellySelectionEventAt index rest

def hellySelectionFromEventFlow (ef : EventFlow) : Option HellySelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HellySelectionUp.mk
      (hellySelectionDecodeBHist (hellySelectionEventAt 0 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 1 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 2 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 3 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 4 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 5 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 6 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 7 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 8 ef))
      (hellySelectionDecodeBHist (hellySelectionEventAt 9 ef)))

private theorem HellySelectionUpTasteGate_single_carrier_alignment_round_trip
    (x : HellySelectionUp) :
    hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
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
      rw [HellySelectionUpTasteGate_single_carrier_alignment_decode_encode B,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode A,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode W,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode S,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode R,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode E,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode T,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode C,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode P,
        HellySelectionUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem HellySelectionUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HellySelectionUp} :
    hellySelectionToEventFlow x = hellySelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hellySelectionFromEventFlow (hellySelectionToEventFlow x) =
        hellySelectionFromEventFlow (hellySelectionToEventFlow y) :=
    congrArg hellySelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HellySelectionUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HellySelectionUpTasteGate_single_carrier_alignment_round_trip y)))

instance hellySelectionBHistCarrier : BHistCarrier HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hellySelectionToEventFlow
  fromEventFlow := hellySelectionFromEventFlow

instance hellySelectionChapterTasteGate : ChapterTasteGate HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x
    exact HellySelectionUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HellySelectionUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HellySelectionUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, hellySelectionDecodeBHist (hellySelectionEncodeBHist h) = h) ∧
      (∀ x : HellySelectionUp,
        hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x) ∧
        (∀ x y : HellySelectionUp,
          hellySelectionToEventFlow x = hellySelectionToEventFlow y → x = y) ∧
          hellySelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HellySelectionUpTasteGate_single_carrier_alignment_decode_encode,
      HellySelectionUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HellySelectionUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HellySelectionUp
