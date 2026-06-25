import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularOpenSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularOpenSetUp : Type where
  | mk (T C R M O K I E D H Q P N : BHist) : RegularOpenSetUp
  deriving DecidableEq

def regularOpenSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularOpenSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularOpenSetEncodeBHist h

def regularOpenSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularOpenSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularOpenSetDecodeBHist tail)

private theorem regularOpenSetDecode_encode :
    ∀ h : BHist, regularOpenSetDecodeBHist (regularOpenSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularOpenSetToEventFlow : RegularOpenSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularOpenSetUp.mk T C R M O K I E D H Q P N =>
      [[BMark.b0],
        regularOpenSetEncodeBHist T,
        [BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularOpenSetEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularOpenSetEncodeBHist N]

private def regularOpenSetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularOpenSetEventAtDefault index rest

def regularOpenSetFromEventFlow (ef : EventFlow) : Option RegularOpenSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularOpenSetUp.mk
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 1 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 3 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 5 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 7 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 9 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 11 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 13 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 15 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 17 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 19 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 21 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 23 ef))
      (regularOpenSetDecodeBHist (regularOpenSetEventAtDefault 25 ef)))

private theorem regularOpenSet_round_trip :
    ∀ x : RegularOpenSetUp,
      regularOpenSetFromEventFlow (regularOpenSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T C R M O K I E D H Q P N =>
      change
        some
          (RegularOpenSetUp.mk
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist T))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist C))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist R))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist M))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist O))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist K))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist I))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist E))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist D))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist H))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist Q))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist P))
            (regularOpenSetDecodeBHist (regularOpenSetEncodeBHist N))) =
          some (RegularOpenSetUp.mk T C R M O K I E D H Q P N)
      rw [regularOpenSetDecode_encode T, regularOpenSetDecode_encode C,
        regularOpenSetDecode_encode R, regularOpenSetDecode_encode M,
        regularOpenSetDecode_encode O, regularOpenSetDecode_encode K,
        regularOpenSetDecode_encode I, regularOpenSetDecode_encode E,
        regularOpenSetDecode_encode D, regularOpenSetDecode_encode H,
        regularOpenSetDecode_encode Q, regularOpenSetDecode_encode P,
        regularOpenSetDecode_encode N]

private theorem regularOpenSetToEventFlow_injective {x y : RegularOpenSetUp} :
    regularOpenSetToEventFlow x = regularOpenSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularOpenSetFromEventFlow (regularOpenSetToEventFlow x) =
        regularOpenSetFromEventFlow (regularOpenSetToEventFlow y) :=
    congrArg regularOpenSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularOpenSet_round_trip x).symm
      (Eq.trans hread (regularOpenSet_round_trip y)))

instance regularOpenSetBHistCarrier : BHistCarrier RegularOpenSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularOpenSetToEventFlow
  fromEventFlow := regularOpenSetFromEventFlow

instance regularOpenSetChapterTasteGate : ChapterTasteGate RegularOpenSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularOpenSetFromEventFlow (regularOpenSetToEventFlow x) = some x
    exact regularOpenSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularOpenSetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularOpenSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularOpenSetChapterTasteGate

theorem RegularOpenSetTasteGate_single_carrier_alignment :
    (forall h : BHist, regularOpenSetDecodeBHist (regularOpenSetEncodeBHist h) = h) ∧
      (forall x : RegularOpenSetUp,
        regularOpenSetFromEventFlow (regularOpenSetToEventFlow x) = some x) ∧
        regularOpenSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨regularOpenSetDecode_encode, regularOpenSet_round_trip, rfl⟩

end BEDC.Derived.RegularOpenSetUp
