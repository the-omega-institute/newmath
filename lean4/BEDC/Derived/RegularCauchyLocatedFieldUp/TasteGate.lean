import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedFieldUp : Type where
  | mk (S W D A M I Q E H C P N : BHist) : RegularCauchyLocatedFieldUp
  deriving DecidableEq

def RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist h

def RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow :
    RegularCauchyLocatedFieldUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedFieldUp.mk S W D A M I Q E H C P N =>
      [RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist S,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist W,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist D,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist A,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist M,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist I,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist Q,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist E,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist H,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist C,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist P,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist N]

private def RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault index rest

def RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option RegularCauchyLocatedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLocatedFieldUp.mk
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyLocatedFieldUp,
      RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fromEventFlow
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D A M I Q E H C P N =>
      change
        some
          (RegularCauchyLocatedFieldUp.mk
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist S))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist W))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist D))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist A))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist M))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist I))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist Q))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist E))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist H))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist C))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist P))
            (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RegularCauchyLocatedFieldUp.mk S W D A M I Q E H C P N)
      rw [RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode I,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyLocatedFieldUp} :
    RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow x =
      RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow x) =
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyLocatedFieldBHistCarrier :
    BHistCarrier RegularCauchyLocatedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fromEventFlow

theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment :
    ChapterTasteGate RegularCauchyLocatedFieldUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fromEventFlow
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyLocatedFieldChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyLocatedFieldTasteGate_single_carrier_alignment

end BEDC.Derived.RegularCauchyLocatedFieldUp
