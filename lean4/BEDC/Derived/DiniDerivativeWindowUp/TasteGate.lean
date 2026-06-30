import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniDerivativeWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniDerivativeWindowUp : Type where
  | mk (I F U L O S R D E H C P N : BHist) : DiniDerivativeWindowUp
  deriving DecidableEq

def DiniDerivativeWindowTasteGate_single_carrier_alignment_fields :
    DiniDerivativeWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniDerivativeWindowUp.mk I F U L O S R D E H C P N =>
      [I, F, U, L, O, S, R, D, E, H, C, P, N]

def DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist h

def DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow :
    DiniDerivativeWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiniDerivativeWindowUp.mk I F U L O S R D E H C P N =>
      [DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist I,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist F,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist U,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist L,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist O,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist S,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist R,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist D,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist E,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist H,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist C,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist P,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist N]

private def DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault index rest

def DiniDerivativeWindowTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option DiniDerivativeWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiniDerivativeWindowUp.mk
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

private theorem DiniDerivativeWindowTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiniDerivativeWindowUp,
      DiniDerivativeWindowTasteGate_single_carrier_alignment_fromEventFlow
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F U L O S R D E H C P N =>
      change
        some
          (DiniDerivativeWindowUp.mk
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist I))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist F))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist U))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist L))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist O))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist S))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist R))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist D))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist E))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist H))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist C))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist P))
            (DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
              (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (DiniDerivativeWindowUp.mk I F U L O S R D E H C P N)
      rw [DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode I,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode F,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode U,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode L,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode O,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode S,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode R,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode D,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode E,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode H,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode C,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode P,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode N]

private theorem DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiniDerivativeWindowUp} :
    DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow x =
      DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DiniDerivativeWindowTasteGate_single_carrier_alignment_fromEventFlow
          (DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow x) =
        DiniDerivativeWindowTasteGate_single_carrier_alignment_fromEventFlow
          (DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DiniDerivativeWindowTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiniDerivativeWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_round_trip y)))

instance DiniDerivativeWindowTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DiniDerivativeWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DiniDerivativeWindowTasteGate_single_carrier_alignment_fromEventFlow

instance DiniDerivativeWindowTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DiniDerivativeWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DiniDerivativeWindowTasteGate_single_carrier_alignment_fromEventFlow
        (DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact DiniDerivativeWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiniDerivativeWindowTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DiniDerivativeWindowTasteGate_single_carrier_alignment :
    (∀ I F U L O S R D E H C P N : BHist,
      DiniDerivativeWindowTasteGate_single_carrier_alignment_fields
        (DiniDerivativeWindowUp.mk I F U L O S R D E H C P N) =
          [I, F, U, L, O, S, R, D, E, H, C, P, N]) ∧
      (∀ h : BHist,
        DiniDerivativeWindowTasteGate_single_carrier_alignment_decodeBHist
          (DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        DiniDerivativeWindowTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro I F U L O S R D E H C P N
    rfl
  · constructor
    · exact DiniDerivativeWindowTasteGate_single_carrier_alignment_decode_encode
    · rfl

end BEDC.Derived.DiniDerivativeWindowUp
