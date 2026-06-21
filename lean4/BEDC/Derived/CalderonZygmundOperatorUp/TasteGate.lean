import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CalderonZygmundOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CalderonZygmundOperatorUp : Type where
  | mk (X W S A L M D E H C P N : BHist) : CalderonZygmundOperatorUp
  deriving DecidableEq

def calderonZygmundOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: calderonZygmundOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: calderonZygmundOperatorEncodeBHist h

def calderonZygmundOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (calderonZygmundOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (calderonZygmundOperatorDecodeBHist tail)

private theorem CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def calderonZygmundOperatorFields : CalderonZygmundOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CalderonZygmundOperatorUp.mk X W S A L M D E H C P N =>
      [X, W, S, A, L, M, D, E, H, C, P, N]

def calderonZygmundOperatorToEventFlow : CalderonZygmundOperatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (calderonZygmundOperatorFields x).map calderonZygmundOperatorEncodeBHist

private def calderonZygmundOperatorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => calderonZygmundOperatorEventAtDefault index rest

def calderonZygmundOperatorFromEventFlow : EventFlow → Option CalderonZygmundOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CalderonZygmundOperatorUp.mk
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 0 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 1 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 2 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 3 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 4 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 5 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 6 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 7 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 8 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 9 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 10 ef))
        (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEventAtDefault 11 ef)))

private theorem CalderonZygmundOperatorUp_single_carrier_alignment_round_trip
    (x : CalderonZygmundOperatorUp) :
    calderonZygmundOperatorFromEventFlow (calderonZygmundOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X W S A L M D E H C P N =>
      change
        some
          (CalderonZygmundOperatorUp.mk
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist X))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist W))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist S))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist A))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist L))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist M))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist D))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist E))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist H))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist C))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist P))
            (calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist N))) =
          some (CalderonZygmundOperatorUp.mk X W S A L M D E H C P N)
      rw [CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode X,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode W,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode S,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode A,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode L,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode M,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode D,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode E,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode H,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode C,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode P,
        CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode N]

private theorem CalderonZygmundOperatorUp_single_carrier_alignment_toEventFlow_injective
    {x y : CalderonZygmundOperatorUp} :
    calderonZygmundOperatorToEventFlow x = calderonZygmundOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          calderonZygmundOperatorFromEventFlow (calderonZygmundOperatorToEventFlow x) :=
        (CalderonZygmundOperatorUp_single_carrier_alignment_round_trip x).symm
      _ = calderonZygmundOperatorFromEventFlow (calderonZygmundOperatorToEventFlow y) :=
        congrArg calderonZygmundOperatorFromEventFlow hxy
      _ = some y := CalderonZygmundOperatorUp_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance calderonZygmundOperatorBHistCarrier :
    BHistCarrier CalderonZygmundOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := calderonZygmundOperatorToEventFlow
  fromEventFlow := calderonZygmundOperatorFromEventFlow

instance calderonZygmundOperatorChapterTasteGate :
    ChapterTasteGate CalderonZygmundOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change calderonZygmundOperatorFromEventFlow (calderonZygmundOperatorToEventFlow x) = some x
    exact CalderonZygmundOperatorUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CalderonZygmundOperatorUp_single_carrier_alignment_toEventFlow_injective heq)

theorem CalderonZygmundOperatorUp_single_carrier_alignment :
    (∀ h : BHist,
      calderonZygmundOperatorDecodeBHist (calderonZygmundOperatorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CalderonZygmundOperatorUp) ∧
        Nonempty (ChapterTasteGate CalderonZygmundOperatorUp) ∧
          calderonZygmundOperatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CalderonZygmundOperatorUp_single_carrier_alignment_decode_encode,
      ⟨calderonZygmundOperatorBHistCarrier⟩,
      ⟨calderonZygmundOperatorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CalderonZygmundOperatorUp
