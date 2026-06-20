import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealArchimedeanFloorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealArchimedeanFloorUp : Type where
  | mk (R Q D Z A L U H C P N : BHist) : RealArchimedeanFloorUp
  deriving DecidableEq

def realArchimedeanFloorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realArchimedeanFloorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realArchimedeanFloorEncodeBHist h

def realArchimedeanFloorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realArchimedeanFloorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realArchimedeanFloorDecodeBHist tail)

private theorem RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realArchimedeanFloorFields : RealArchimedeanFloorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealArchimedeanFloorUp.mk R Q D Z A L U H C P N => [R, Q, D, Z, A, L, U, H, C, P, N]

def realArchimedeanFloorToEventFlow : RealArchimedeanFloorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realArchimedeanFloorFields x).map realArchimedeanFloorEncodeBHist

private def RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt index rest

def realArchimedeanFloorFromEventFlow (ef : EventFlow) : Option RealArchimedeanFloorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealArchimedeanFloorUp.mk
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 0 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 1 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 2 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 3 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 4 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 5 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 6 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 7 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 8 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 9 ef))
      (realArchimedeanFloorDecodeBHist
        (RealArchimedeanFloorTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem RealArchimedeanFloorTasteGate_single_carrier_alignment_round_trip
    (x : RealArchimedeanFloorUp) :
    realArchimedeanFloorFromEventFlow (realArchimedeanFloorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R Q D Z A L U H C P N =>
      change
        some
          (RealArchimedeanFloorUp.mk
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist R))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist Q))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist D))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist Z))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist A))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist L))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist U))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist H))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist C))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist P))
            (realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist N))) =
          some (RealArchimedeanFloorUp.mk R Q D Z A L U H C P N)
      rw [RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode R,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode Q,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode D,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode Z,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode A,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode L,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode U,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode H,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode C,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode P,
        RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealArchimedeanFloorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealArchimedeanFloorUp} :
    realArchimedeanFloorToEventFlow x = realArchimedeanFloorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realArchimedeanFloorFromEventFlow (realArchimedeanFloorToEventFlow x) =
        realArchimedeanFloorFromEventFlow (realArchimedeanFloorToEventFlow y) :=
    congrArg realArchimedeanFloorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealArchimedeanFloorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealArchimedeanFloorTasteGate_single_carrier_alignment_round_trip y)))

instance realArchimedeanFloorBHistCarrier : BHistCarrier RealArchimedeanFloorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realArchimedeanFloorToEventFlow
  fromEventFlow := realArchimedeanFloorFromEventFlow

instance realArchimedeanFloorChapterTasteGate : ChapterTasteGate RealArchimedeanFloorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realArchimedeanFloorFromEventFlow (realArchimedeanFloorToEventFlow x) = some x
    exact RealArchimedeanFloorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealArchimedeanFloorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealArchimedeanFloorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realArchimedeanFloorChapterTasteGate

theorem RealArchimedeanFloorTasteGate_single_carrier_alignment :
    (∀ h : BHist, realArchimedeanFloorDecodeBHist (realArchimedeanFloorEncodeBHist h) = h) ∧
      (∀ x : RealArchimedeanFloorUp,
        realArchimedeanFloorFromEventFlow (realArchimedeanFloorToEventFlow x) = some x) ∧
        (∀ x y : RealArchimedeanFloorUp,
          realArchimedeanFloorToEventFlow x = realArchimedeanFloorToEventFlow y → x = y) ∧
          realArchimedeanFloorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealArchimedeanFloorTasteGate_single_carrier_alignment_decode_encode,
      RealArchimedeanFloorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealArchimedeanFloorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealArchimedeanFloorUp
