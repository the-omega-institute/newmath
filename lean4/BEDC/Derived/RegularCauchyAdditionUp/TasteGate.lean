import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyAdditionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyAdditionUp : Type where
  | mk (R0 R1 W0 W1 T0 T1 D S E Z H C P N : BHist) : RegularCauchyAdditionUp
  deriving DecidableEq

def regularCauchyAdditionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyAdditionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyAdditionEncodeBHist h

def regularCauchyAdditionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyAdditionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyAdditionDecodeBHist tail)

private theorem regularCauchyAdditionDecode_encode_bhist :
    forall h : BHist,
      regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyAdditionToEventFlow : RegularCauchyAdditionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C P N =>
      [[BMark.b0],
        regularCauchyAdditionEncodeBHist R0,
        [BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist W0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist W1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist T0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist T1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyAdditionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyAdditionEncodeBHist N]

private def regularCauchyAdditionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, row :: _ => row
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyAdditionEventAtDefault n rest

def regularCauchyAdditionFromEventFlow (ef : EventFlow) : Option RegularCauchyAdditionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyAdditionUp.mk
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 1 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 3 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 5 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 7 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 9 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 11 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 13 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 15 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 17 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 19 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 21 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 23 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 25 ef))
      (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEventAtDefault 27 ef)))

private theorem regularCauchyAddition_round_trip :
    forall x : RegularCauchyAdditionUp,
      regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 W0 W1 T0 T1 D S E Z H C P N =>
      change
        some
          (RegularCauchyAdditionUp.mk
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist R0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist R1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N))) =
          some (RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C P N)
      exact congrArg some (calc
        RegularCauchyAdditionUp.mk
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist R0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist R1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) =
          RegularCauchyAdditionUp.mk R0
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist R1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist R1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W0))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist R0)
        _ = RegularCauchyAdditionUp.mk R0 R1
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W0))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist R1)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist W1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist W0)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T0))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist W1)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist T1))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist T0)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist D))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist T1)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist S))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist D)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist E))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist S)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist Z))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist E)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist H))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist Z)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist C))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist H)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist P))
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist C)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C P
            (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)) :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C z
              (regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist N)))
            (regularCauchyAdditionDecode_encode_bhist P)
        _ = RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C P N :=
          congrArg
            (fun z => RegularCauchyAdditionUp.mk R0 R1 W0 W1 T0 T1 D S E Z H C P z)
            (regularCauchyAdditionDecode_encode_bhist N))

private theorem regularCauchyAdditionToEventFlow_injective {x y : RegularCauchyAdditionUp} :
    regularCauchyAdditionToEventFlow x = regularCauchyAdditionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) =
        regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow y) :=
    congrArg regularCauchyAdditionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyAddition_round_trip x).symm
      (Eq.trans hread (regularCauchyAddition_round_trip y)))

instance regularCauchyAdditionBHistCarrier : BHistCarrier RegularCauchyAdditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyAdditionToEventFlow
  fromEventFlow := regularCauchyAdditionFromEventFlow

instance regularCauchyAdditionChapterTasteGate : ChapterTasteGate RegularCauchyAdditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) = some x
    exact regularCauchyAddition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyAdditionToEventFlow_injective heq)

theorem RegularCauchyAdditionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyAdditionDecodeBHist (regularCauchyAdditionEncodeBHist h) = h) /\
      (forall x : RegularCauchyAdditionUp,
        regularCauchyAdditionFromEventFlow (regularCauchyAdditionToEventFlow x) = some x) /\
        (forall x y : RegularCauchyAdditionUp,
          regularCauchyAdditionToEventFlow x = regularCauchyAdditionToEventFlow y -> x = y) /\
          regularCauchyAdditionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyAdditionDecode_encode_bhist
  · constructor
    · exact regularCauchyAddition_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyAdditionToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyAdditionUp
