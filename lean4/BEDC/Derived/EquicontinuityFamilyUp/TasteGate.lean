import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuityFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuityFamilyUp : Type where
  | mk (X Y F P R M H C V N : BHist) : EquicontinuityFamilyUp
  deriving DecidableEq

def EquicontinuityFamilyTasteGate_single_carrier_alignment_encode :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: EquicontinuityFamilyTasteGate_single_carrier_alignment_encode h
  | BHist.e1 h => BMark.b1 :: EquicontinuityFamilyTasteGate_single_carrier_alignment_encode h

def EquicontinuityFamilyTasteGate_single_carrier_alignment_decode :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode tail)
  | BMark.b1 :: tail =>
      BHist.e1 (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode tail)

private theorem EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist,
      EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def EquicontinuityFamilyTasteGate_single_carrier_alignment_fields :
    EquicontinuityFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuityFamilyUp.mk X Y F P R M H C V N => [X, Y, F, P, R, M, H, C, V, N]

def EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow :
    EquicontinuityFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_fields x).map
        EquicontinuityFamilyTasteGate_single_carrier_alignment_encode

private def EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at index rest

def EquicontinuityFamilyTasteGate_single_carrier_alignment_from_event_flow
    (ef : EventFlow) : Option EquicontinuityFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EquicontinuityFamilyUp.mk
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 0 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 1 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 2 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 3 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 4 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 5 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 6 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 7 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 8 ef))
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_event_at 9 ef)))

private theorem EquicontinuityFamilyTasteGate_single_carrier_alignment_round_trip
    (x : EquicontinuityFamilyUp) :
    EquicontinuityFamilyTasteGate_single_carrier_alignment_from_event_flow
      (EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y F P R M H C V N =>
      change
        some
          (EquicontinuityFamilyUp.mk
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode X))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode Y))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode F))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode P))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode R))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode M))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode H))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode C))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode V))
            (EquicontinuityFamilyTasteGate_single_carrier_alignment_decode
              (EquicontinuityFamilyTasteGate_single_carrier_alignment_encode N))) =
          some (EquicontinuityFamilyUp.mk X Y F P R M H C V N)
      rw [EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux X,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux Y,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux F,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux P,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux R,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux M,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux H,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux C,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux V,
        EquicontinuityFamilyTasteGate_single_carrier_alignment_decode_aux N]

private theorem EquicontinuityFamilyTasteGate_single_carrier_alignment_injective_aux
    {x y : EquicontinuityFamilyUp} :
    EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow x =
      EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      EquicontinuityFamilyTasteGate_single_carrier_alignment_from_event_flow
          (EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow x) =
        EquicontinuityFamilyTasteGate_single_carrier_alignment_from_event_flow
          (EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow y) :=
    congrArg EquicontinuityFamilyTasteGate_single_carrier_alignment_from_event_flow heq
  exact Option.some.inj
    (Eq.trans (EquicontinuityFamilyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EquicontinuityFamilyTasteGate_single_carrier_alignment_round_trip y)))

instance EquicontinuityFamilyTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier EquicontinuityFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow
  fromEventFlow := EquicontinuityFamilyTasteGate_single_carrier_alignment_from_event_flow

instance EquicontinuityFamilyTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate EquicontinuityFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      EquicontinuityFamilyTasteGate_single_carrier_alignment_from_event_flow
        (EquicontinuityFamilyTasteGate_single_carrier_alignment_to_event_flow x) = some x
    exact EquicontinuityFamilyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EquicontinuityFamilyTasteGate_single_carrier_alignment_injective_aux heq)

def EquicontinuityFamilyTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate EquicontinuityFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  EquicontinuityFamilyTasteGate_single_carrier_alignment_ChapterTasteGate

theorem EquicontinuityFamilyTasteGate_single_carrier_alignment :
    ChapterTasteGate EquicontinuityFamilyUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact EquicontinuityFamilyTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.EquicontinuityFamilyUp
