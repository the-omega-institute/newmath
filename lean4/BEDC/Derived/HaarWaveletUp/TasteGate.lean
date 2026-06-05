import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaarWaveletUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaarWaveletUp : Type where
  | mk (K I L V A B R E H C P N : BHist) : HaarWaveletUp
  deriving DecidableEq

def haarWaveletEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haarWaveletEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haarWaveletEncodeBHist h

def haarWaveletDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haarWaveletDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haarWaveletDecodeBHist tail)

private theorem HaarWaveletTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, haarWaveletDecodeBHist (haarWaveletEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def haarWaveletFields : HaarWaveletUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HaarWaveletUp.mk K I L V A B R E H C P N => [K, I, L, V, A, B, R, E, H, C, P, N]

def haarWaveletToEventFlow : HaarWaveletUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (haarWaveletFields x).map haarWaveletEncodeBHist

private def haarWaveletEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => haarWaveletEventAt index rest

def haarWaveletFromEventFlow : EventFlow → Option HaarWaveletUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (HaarWaveletUp.mk
        (haarWaveletDecodeBHist (haarWaveletEventAt 0 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 1 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 2 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 3 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 4 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 5 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 6 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 7 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 8 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 9 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 10 flow))
        (haarWaveletDecodeBHist (haarWaveletEventAt 11 flow)))

private theorem HaarWaveletTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HaarWaveletUp,
      haarWaveletFromEventFlow (haarWaveletToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K I L V A B R E H C P N =>
      change
        some
          (HaarWaveletUp.mk
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist K))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist I))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist L))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist V))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist A))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist B))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist R))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist E))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist H))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist C))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist P))
            (haarWaveletDecodeBHist (haarWaveletEncodeBHist N))) =
          some (HaarWaveletUp.mk K I L V A B R E H C P N)
      rw [HaarWaveletTasteGate_single_carrier_alignment_decode_encode K,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode I,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode L,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode V,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode A,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode B,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode R,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode E,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode H,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode C,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode P,
        HaarWaveletTasteGate_single_carrier_alignment_decode_encode N]

private theorem HaarWaveletTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HaarWaveletUp} :
    haarWaveletToEventFlow x = haarWaveletToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haarWaveletFromEventFlow (haarWaveletToEventFlow x) =
        haarWaveletFromEventFlow (haarWaveletToEventFlow y) :=
    congrArg haarWaveletFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HaarWaveletTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HaarWaveletTasteGate_single_carrier_alignment_round_trip y)))

instance haarWaveletBHistCarrier : BHistCarrier HaarWaveletUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haarWaveletToEventFlow
  fromEventFlow := haarWaveletFromEventFlow

instance haarWaveletChapterTasteGate : ChapterTasteGate HaarWaveletUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change haarWaveletFromEventFlow (haarWaveletToEventFlow x) = some x
    exact HaarWaveletTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HaarWaveletTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HaarWaveletUp :=
  -- BEDC touchpoint anchor: BHist BMark
  haarWaveletChapterTasteGate

theorem HaarWaveletTasteGate_single_carrier_alignment :
    (forall h : BHist, haarWaveletDecodeBHist (haarWaveletEncodeBHist h) = h) ∧
      (forall x : HaarWaveletUp,
        haarWaveletFromEventFlow (haarWaveletToEventFlow x) = some x) ∧
        Nonempty (BHistCarrier HaarWaveletUp) ∧
          Nonempty (ChapterTasteGate HaarWaveletUp) ∧
            haarWaveletEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact HaarWaveletTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HaarWaveletTasteGate_single_carrier_alignment_round_trip
    · constructor
      · exact ⟨haarWaveletBHistCarrier⟩
      · constructor
        · exact ⟨haarWaveletChapterTasteGate⟩
        · rfl

end BEDC.Derived.HaarWaveletUp
