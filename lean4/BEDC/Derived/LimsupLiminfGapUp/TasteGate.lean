import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimsupLiminfGapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimsupLiminfGapUp : Type where
  | mk (S I U D Q E H C P N : BHist) : LimsupLiminfGapUp
  deriving DecidableEq

def limsupLiminfGapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limsupLiminfGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limsupLiminfGapEncodeBHist h

def limsupLiminfGapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limsupLiminfGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limsupLiminfGapDecodeBHist tail)

private theorem limsupLiminfGap_decode_encode :
    ∀ h : BHist, limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limsupLiminfGapToEventFlow : LimsupLiminfGapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LimsupLiminfGapUp.mk S I U D Q E H C P N =>
      [limsupLiminfGapEncodeBHist S,
        limsupLiminfGapEncodeBHist I,
        limsupLiminfGapEncodeBHist U,
        limsupLiminfGapEncodeBHist D,
        limsupLiminfGapEncodeBHist Q,
        limsupLiminfGapEncodeBHist E,
        limsupLiminfGapEncodeBHist H,
        limsupLiminfGapEncodeBHist C,
        limsupLiminfGapEncodeBHist P,
        limsupLiminfGapEncodeBHist N]

private def limsupLiminfGapEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => limsupLiminfGapEventAt index rest

def limsupLiminfGapFromEventFlow (ef : EventFlow) : Option LimsupLiminfGapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LimsupLiminfGapUp.mk
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 0 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 1 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 2 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 3 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 4 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 5 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 6 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 7 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 8 ef))
      (limsupLiminfGapDecodeBHist (limsupLiminfGapEventAt 9 ef)))

private theorem limsupLiminfGap_round_trip (x : LimsupLiminfGapUp) :
    limsupLiminfGapFromEventFlow (limsupLiminfGapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S I U D Q E H C P N =>
      change
        some
          (LimsupLiminfGapUp.mk
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist S))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist I))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist U))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist D))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist Q))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist E))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist H))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist C))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist P))
            (limsupLiminfGapDecodeBHist (limsupLiminfGapEncodeBHist N))) =
          some (LimsupLiminfGapUp.mk S I U D Q E H C P N)
      rw [limsupLiminfGap_decode_encode S, limsupLiminfGap_decode_encode I,
        limsupLiminfGap_decode_encode U, limsupLiminfGap_decode_encode D,
        limsupLiminfGap_decode_encode Q, limsupLiminfGap_decode_encode E,
        limsupLiminfGap_decode_encode H, limsupLiminfGap_decode_encode C,
        limsupLiminfGap_decode_encode P, limsupLiminfGap_decode_encode N]

private theorem limsupLiminfGapToEventFlow_injective {x y : LimsupLiminfGapUp} :
    limsupLiminfGapToEventFlow x = limsupLiminfGapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limsupLiminfGapFromEventFlow (limsupLiminfGapToEventFlow x) =
        limsupLiminfGapFromEventFlow (limsupLiminfGapToEventFlow y) :=
    congrArg limsupLiminfGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (limsupLiminfGap_round_trip x).symm
      (Eq.trans hread (limsupLiminfGap_round_trip y)))

instance limsupLiminfGapBHistCarrier : BHistCarrier LimsupLiminfGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limsupLiminfGapToEventFlow
  fromEventFlow := limsupLiminfGapFromEventFlow

instance limsupLiminfGapChapterTasteGate : ChapterTasteGate LimsupLiminfGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limsupLiminfGapFromEventFlow (limsupLiminfGapToEventFlow x) = some x
    exact limsupLiminfGap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (limsupLiminfGapToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LimsupLiminfGapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  limsupLiminfGapChapterTasteGate

theorem LimsupLiminfGapTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LimsupLiminfGapUp) ∧
      Nonempty (ChapterTasteGate LimsupLiminfGapUp) ∧
        limsupLiminfGapEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨limsupLiminfGapBHistCarrier⟩, ⟨limsupLiminfGapChapterTasteGate⟩, rfl⟩

end BEDC.Derived.LimsupLiminfGapUp
