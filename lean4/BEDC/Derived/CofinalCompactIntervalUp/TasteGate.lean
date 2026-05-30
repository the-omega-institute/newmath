import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalCompactIntervalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalCompactIntervalUp : Type where
  | mk (I L D W R E H C P N : BHist) : CofinalCompactIntervalUp
  deriving DecidableEq

def cofinalCompactIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalCompactIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalCompactIntervalEncodeBHist h

def cofinalCompactIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalCompactIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalCompactIntervalDecodeBHist tail)

private theorem CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cofinalCompactIntervalFields : CofinalCompactIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalCompactIntervalUp.mk I L D W R E H C P N => [I, L, D, W, R, E, H, C, P, N]

def cofinalCompactIntervalToEventFlow : CofinalCompactIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cofinalCompactIntervalFields x).map cofinalCompactIntervalEncodeBHist

private def CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt index rest

def cofinalCompactIntervalDecodeFields (ef : EventFlow) : CofinalCompactIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CofinalCompactIntervalUp.mk
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 0 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 1 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 2 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 3 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 4 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 5 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 6 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 7 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 8 ef))
    (cofinalCompactIntervalDecodeBHist
      (CofinalCompactIntervalTasteGate_single_carrier_alignment_eventAt 9 ef))

def cofinalCompactIntervalFromEventFlow (ef : EventFlow) : Option CofinalCompactIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (cofinalCompactIntervalDecodeFields ef)

private theorem CofinalCompactIntervalTasteGate_single_carrier_alignment_round_trip
    (x : CofinalCompactIntervalUp) :
    cofinalCompactIntervalFromEventFlow (cofinalCompactIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I L D W R E H C P N =>
      change
        some
          (CofinalCompactIntervalUp.mk
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist I))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist L))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist D))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist W))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist R))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist E))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist H))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist C))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist P))
            (cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist N))) =
          some (CofinalCompactIntervalUp.mk I L D W R E H C P N)
      rw [CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode I,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode L,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode D,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode W,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode R,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode E,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode H,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode C,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode P,
        CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode N]

private theorem CofinalCompactIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CofinalCompactIntervalUp} :
    cofinalCompactIntervalToEventFlow x = cofinalCompactIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalCompactIntervalFromEventFlow (cofinalCompactIntervalToEventFlow x) =
        cofinalCompactIntervalFromEventFlow (cofinalCompactIntervalToEventFlow y) :=
    congrArg cofinalCompactIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CofinalCompactIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CofinalCompactIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance cofinalCompactIntervalBHistCarrier :
    BHistCarrier CofinalCompactIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalCompactIntervalToEventFlow
  fromEventFlow := cofinalCompactIntervalFromEventFlow

instance cofinalCompactIntervalChapterTasteGate :
    ChapterTasteGate CofinalCompactIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cofinalCompactIntervalFromEventFlow (cofinalCompactIntervalToEventFlow x) = some x
    exact CofinalCompactIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CofinalCompactIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CofinalCompactIntervalTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CofinalCompactIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalCompactIntervalChapterTasteGate

theorem CofinalCompactIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cofinalCompactIntervalDecodeBHist (cofinalCompactIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CofinalCompactIntervalUp) ∧
        Nonempty (ChapterTasteGate CofinalCompactIntervalUp) ∧
          cofinalCompactIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CofinalCompactIntervalTasteGate_single_carrier_alignment_decode_encode,
      ⟨cofinalCompactIntervalBHistCarrier⟩,
      ⟨cofinalCompactIntervalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CofinalCompactIntervalUp.TasteGate
