import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HoeffdingFiniteSumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HoeffdingFiniteSumUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (P V I B S D E H C Q N : BHist) : HoeffdingFiniteSumUp

def hoeffdingFiniteSumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hoeffdingFiniteSumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hoeffdingFiniteSumEncodeBHist h

def hoeffdingFiniteSumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hoeffdingFiniteSumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hoeffdingFiniteSumDecodeBHist tail)

private theorem HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def HoeffdingFiniteSumTasteGate_single_carrier_alignment_fields :
    HoeffdingFiniteSumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HoeffdingFiniteSumUp.mk P V I B S D E H C Q N => [P, V, I, B, S, D, E, H, C, Q, N]

def HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow :
    HoeffdingFiniteSumUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (HoeffdingFiniteSumTasteGate_single_carrier_alignment_fields x).map
      hoeffdingFiniteSumEncodeBHist

private def hoeffdingFiniteSumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hoeffdingFiniteSumEventAtDefault index rest

def HoeffdingFiniteSumTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option HoeffdingFiniteSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (HoeffdingFiniteSumUp.mk
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 0 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 1 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 2 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 3 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 4 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 5 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 6 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 7 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 8 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 9 ef))
        (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEventAtDefault 10 ef)))

private theorem HoeffdingFiniteSumTasteGate_single_carrier_alignment_round_trip
    (x : HoeffdingFiniteSumUp) :
    HoeffdingFiniteSumTasteGate_single_carrier_alignment_fromEventFlow
      (HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P V I B S D E H C Q N =>
      change
        some
          (HoeffdingFiniteSumUp.mk
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist P))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist V))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist I))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist B))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist S))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist D))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist E))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist H))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist C))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist Q))
            (hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist N))) =
          some (HoeffdingFiniteSumUp.mk P V I B S D E H C Q N)
      rw [HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode P,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode V,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode I,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode B,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode S,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode D,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode E,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode H,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode C,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode Q,
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode N]

private theorem HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HoeffdingFiniteSumUp} :
    HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow x =
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      HoeffdingFiniteSumTasteGate_single_carrier_alignment_fromEventFlow
          (HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow x) =
        HoeffdingFiniteSumTasteGate_single_carrier_alignment_fromEventFlow
          (HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg HoeffdingFiniteSumTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HoeffdingFiniteSumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HoeffdingFiniteSumTasteGate_single_carrier_alignment_round_trip y)))

instance hoeffdingFiniteSumBHistCarrier : BHistCarrier HoeffdingFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := HoeffdingFiniteSumTasteGate_single_carrier_alignment_fromEventFlow

instance hoeffdingFiniteSumChapterTasteGate : ChapterTasteGate HoeffdingFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      HoeffdingFiniteSumTasteGate_single_carrier_alignment_fromEventFlow
        (HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact HoeffdingFiniteSumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HoeffdingFiniteSumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HoeffdingFiniteSumTasteGate_single_carrier_alignment :
    (∀ h : BHist, hoeffdingFiniteSumDecodeBHist (hoeffdingFiniteSumEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HoeffdingFiniteSumUp) ∧
      Nonempty (ChapterTasteGate HoeffdingFiniteSumUp) ∧
      hoeffdingFiniteSumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact HoeffdingFiniteSumTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨hoeffdingFiniteSumBHistCarrier⟩
    · constructor
      · exact ⟨hoeffdingFiniteSumChapterTasteGate⟩
      · rfl

end BEDC.Derived.HoeffdingFiniteSumUp
