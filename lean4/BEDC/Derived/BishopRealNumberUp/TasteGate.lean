import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealNumberUp : Type where
  | mk (S R D E M H C P N : BHist) : BishopRealNumberUp
  deriving DecidableEq

def bishopRealNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealNumberEncodeBHist h

def bishopRealNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealNumberDecodeBHist tail)

private theorem bishopRealNumberDecode_encode_bhist :
    ∀ h : BHist, bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealNumberFields : BishopRealNumberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealNumberUp.mk S R D E M H C P N => [S, R, D, E, M, H, C, P, N]

def bishopRealNumberToEventFlow : BishopRealNumberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealNumberFields x).map bishopRealNumberEncodeBHist

private def bishopRealNumberEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealNumberEventAt index rest

def bishopRealNumberFromEventFlow (ef : EventFlow) : Option BishopRealNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealNumberUp.mk
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 0 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 1 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 2 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 3 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 4 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 5 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 6 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 7 ef))
      (bishopRealNumberDecodeBHist (bishopRealNumberEventAt 8 ef)))

private theorem bishopRealNumber_round_trip :
    ∀ x : BishopRealNumberUp,
      bishopRealNumberFromEventFlow (bishopRealNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D E M H C P N =>
      change
        some
          (BishopRealNumberUp.mk
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist S))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist R))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist D))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist E))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist M))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist H))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist C))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist P))
            (bishopRealNumberDecodeBHist (bishopRealNumberEncodeBHist N))) =
          some (BishopRealNumberUp.mk S R D E M H C P N)
      rw [bishopRealNumberDecode_encode_bhist S, bishopRealNumberDecode_encode_bhist R,
        bishopRealNumberDecode_encode_bhist D, bishopRealNumberDecode_encode_bhist E,
        bishopRealNumberDecode_encode_bhist M, bishopRealNumberDecode_encode_bhist H,
        bishopRealNumberDecode_encode_bhist C, bishopRealNumberDecode_encode_bhist P,
        bishopRealNumberDecode_encode_bhist N]

private theorem bishopRealNumberToEventFlow_injective {x y : BishopRealNumberUp} :
    bishopRealNumberToEventFlow x = bishopRealNumberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealNumberFromEventFlow (bishopRealNumberToEventFlow x) =
        bishopRealNumberFromEventFlow (bishopRealNumberToEventFlow y) :=
    congrArg bishopRealNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRealNumber_round_trip x).symm
      (Eq.trans hread (bishopRealNumber_round_trip y)))

instance bishopRealNumberBHistCarrier : BHistCarrier BishopRealNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealNumberToEventFlow
  fromEventFlow := bishopRealNumberFromEventFlow

instance bishopRealNumberChapterTasteGate : ChapterTasteGate BishopRealNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealNumberFromEventFlow (bishopRealNumberToEventFlow x) = some x
    exact bishopRealNumber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRealNumberToEventFlow_injective heq)

theorem BishopRealNumberTasteGate_single_carrier_alignment :
    ChapterTasteGate BishopRealNumberUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact bishopRealNumberChapterTasteGate

end BEDC.Derived.BishopRealNumberUp
