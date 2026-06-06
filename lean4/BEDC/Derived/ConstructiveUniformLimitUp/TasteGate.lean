import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveUniformLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveUniformLimitUp : Type where
  | mk (A L W R E H C P N : BHist) : ConstructiveUniformLimitUp
  deriving DecidableEq

def ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist h

def ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
          (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ConstructiveUniformLimitTasteGate_single_carrier_alignment_fields :
    ConstructiveUniformLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveUniformLimitUp.mk A L W R E H C P N => [A, L, W, R, E, H, C, P, N]

def ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow :
    ConstructiveUniformLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (ConstructiveUniformLimitTasteGate_single_carrier_alignment_fields x).map
      ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist

private def ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt index rest

def ConstructiveUniformLimitTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option ConstructiveUniformLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveUniformLimitUp.mk
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 0 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 1 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 2 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 3 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 4 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 5 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 6 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 7 ef))
      (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem ConstructiveUniformLimitTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveUniformLimitUp) :
    ConstructiveUniformLimitTasteGate_single_carrier_alignment_fromEventFlow
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A L W R E H C P N =>
      change
        some
          (ConstructiveUniformLimitUp.mk
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist A))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist L))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist W))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist R))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist E))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist H))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist C))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist P))
            (ConstructiveUniformLimitTasteGate_single_carrier_alignment_decodeBHist
              (ConstructiveUniformLimitTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ConstructiveUniformLimitUp.mk A L W R E H C P N)
      rw [ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode A,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode L,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode W,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveUniformLimitUp} :
    ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow x =
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ConstructiveUniformLimitTasteGate_single_carrier_alignment_fromEventFlow
          (ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        ConstructiveUniformLimitTasteGate_single_carrier_alignment_fromEventFlow
          (ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ConstructiveUniformLimitTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConstructiveUniformLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveUniformLimitTasteGate_single_carrier_alignment_round_trip y)))

instance ConstructiveUniformLimitTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ConstructiveUniformLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ConstructiveUniformLimitTasteGate_single_carrier_alignment_fromEventFlow

instance ConstructiveUniformLimitTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ConstructiveUniformLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ConstructiveUniformLimitTasteGate_single_carrier_alignment_fromEventFlow
          (ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact ConstructiveUniformLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstructiveUniformLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ConstructiveUniformLimitTasteGate_single_carrier_alignment :
    ChapterTasteGate ConstructiveUniformLimitUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ConstructiveUniformLimitTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.ConstructiveUniformLimitUp
