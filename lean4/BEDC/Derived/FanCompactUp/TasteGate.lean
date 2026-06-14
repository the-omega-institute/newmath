import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FanCompactUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (B L T W R I H C P N : BHist) : FanCompactUp
  deriving DecidableEq

def fanCompactEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fanCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fanCompactEncodeBHist h

def fanCompactDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fanCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fanCompactDecodeBHist tail)

private theorem FanCompactTasteGate_single_carrier_alignment_decode :
    forall h : BHist, fanCompactDecodeBHist (fanCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fanCompactFields : FanCompactUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanCompactUp.mk B L T W R I H C P N => [B, L, T, W, R, I, H, C, P, N]

def fanCompactToEventFlow : FanCompactUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fanCompactFields x).map fanCompactEncodeBHist

private def fanCompactEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fanCompactEventAtDefault index rest

def fanCompactFromEventFlow (ef : EventFlow) : Option FanCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FanCompactUp.mk
      (fanCompactDecodeBHist (fanCompactEventAtDefault 0 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 1 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 2 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 3 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 4 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 5 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 6 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 7 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 8 ef))
      (fanCompactDecodeBHist (fanCompactEventAtDefault 9 ef)))

private theorem FanCompactTasteGate_single_carrier_alignment_round_trip :
    forall x : FanCompactUp, fanCompactFromEventFlow (fanCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L T W R I H C P N =>
      change
        some
          (FanCompactUp.mk
            (fanCompactDecodeBHist (fanCompactEncodeBHist B))
            (fanCompactDecodeBHist (fanCompactEncodeBHist L))
            (fanCompactDecodeBHist (fanCompactEncodeBHist T))
            (fanCompactDecodeBHist (fanCompactEncodeBHist W))
            (fanCompactDecodeBHist (fanCompactEncodeBHist R))
            (fanCompactDecodeBHist (fanCompactEncodeBHist I))
            (fanCompactDecodeBHist (fanCompactEncodeBHist H))
            (fanCompactDecodeBHist (fanCompactEncodeBHist C))
            (fanCompactDecodeBHist (fanCompactEncodeBHist P))
            (fanCompactDecodeBHist (fanCompactEncodeBHist N))) =
          some (FanCompactUp.mk B L T W R I H C P N)
      rw [FanCompactTasteGate_single_carrier_alignment_decode B,
        FanCompactTasteGate_single_carrier_alignment_decode L,
        FanCompactTasteGate_single_carrier_alignment_decode T,
        FanCompactTasteGate_single_carrier_alignment_decode W,
        FanCompactTasteGate_single_carrier_alignment_decode R,
        FanCompactTasteGate_single_carrier_alignment_decode I,
        FanCompactTasteGate_single_carrier_alignment_decode H,
        FanCompactTasteGate_single_carrier_alignment_decode C,
        FanCompactTasteGate_single_carrier_alignment_decode P,
        FanCompactTasteGate_single_carrier_alignment_decode N]

private theorem FanCompactTasteGate_single_carrier_alignment_injective {x y : FanCompactUp} :
    fanCompactToEventFlow x = fanCompactToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fanCompactFromEventFlow (fanCompactToEventFlow x) =
        fanCompactFromEventFlow (fanCompactToEventFlow y) :=
    congrArg fanCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FanCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FanCompactTasteGate_single_carrier_alignment_round_trip y)))

instance fanCompactBHistCarrier : BHistCarrier FanCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fanCompactToEventFlow
  fromEventFlow := fanCompactFromEventFlow

instance fanCompactChapterTasteGate : ChapterTasteGate FanCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanCompactFromEventFlow (fanCompactToEventFlow x) = some x
    exact FanCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FanCompactTasteGate_single_carrier_alignment_injective heq)

theorem FanCompactTasteGate_single_carrier_alignment :
    (forall h : BHist, fanCompactDecodeBHist (fanCompactEncodeBHist h) = h) /\
      Nonempty (BHistCarrier FanCompactUp) /\
        Nonempty (ChapterTasteGate FanCompactUp) /\
          fanCompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FanCompactTasteGate_single_carrier_alignment_decode,
      ⟨fanCompactBHistCarrier⟩,
      ⟨fanCompactChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FanCompactUp
