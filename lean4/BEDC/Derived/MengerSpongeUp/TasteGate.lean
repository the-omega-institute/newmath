import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MengerSpongeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MengerSpongeUp : Type where
  | mk (C D B A W Q E H T P N : BHist) : MengerSpongeUp

def mengerSpongeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mengerSpongeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mengerSpongeEncodeBHist h

def mengerSpongeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mengerSpongeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mengerSpongeDecodeBHist tail)

private theorem mengerSpongeDecode_encode_bhist :
    ∀ h : BHist, mengerSpongeDecodeBHist (mengerSpongeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mengerSpongeFields : MengerSpongeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MengerSpongeUp.mk C D B A W Q E H T P N => [C, D, B, A, W, Q, E, H, T, P, N]

def mengerSpongeToEventFlow : MengerSpongeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (mengerSpongeFields x).map mengerSpongeEncodeBHist

private def mengerSpongeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mengerSpongeEventAtDefault index rest

def mengerSpongeFromEventFlow (ef : EventFlow) : Option MengerSpongeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MengerSpongeUp.mk
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 0 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 1 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 2 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 3 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 4 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 5 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 6 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 7 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 8 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 9 ef))
      (mengerSpongeDecodeBHist (mengerSpongeEventAtDefault 10 ef)))

private theorem mengerSponge_round_trip (x : MengerSpongeUp) :
    mengerSpongeFromEventFlow (mengerSpongeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C D B A W Q E H T P N =>
      change
        some
          (MengerSpongeUp.mk
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist C))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist D))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist B))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist A))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist W))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist Q))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist E))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist H))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist T))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist P))
            (mengerSpongeDecodeBHist (mengerSpongeEncodeBHist N))) =
          some (MengerSpongeUp.mk C D B A W Q E H T P N)
      rw [mengerSpongeDecode_encode_bhist C,
        mengerSpongeDecode_encode_bhist D,
        mengerSpongeDecode_encode_bhist B,
        mengerSpongeDecode_encode_bhist A,
        mengerSpongeDecode_encode_bhist W,
        mengerSpongeDecode_encode_bhist Q,
        mengerSpongeDecode_encode_bhist E,
        mengerSpongeDecode_encode_bhist H,
        mengerSpongeDecode_encode_bhist T,
        mengerSpongeDecode_encode_bhist P,
        mengerSpongeDecode_encode_bhist N]

private theorem mengerSpongeToEventFlow_injective {x y : MengerSpongeUp} :
    mengerSpongeToEventFlow x = mengerSpongeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = mengerSpongeFromEventFlow (mengerSpongeToEventFlow x) :=
        (mengerSponge_round_trip x).symm
      _ = mengerSpongeFromEventFlow (mengerSpongeToEventFlow y) :=
        congrArg mengerSpongeFromEventFlow hxy
      _ = some y := mengerSponge_round_trip y
  exact Option.some.inj optionEq

instance mengerSpongeBHistCarrier : BHistCarrier MengerSpongeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mengerSpongeToEventFlow
  fromEventFlow := mengerSpongeFromEventFlow

instance mengerSpongeChapterTasteGate : ChapterTasteGate MengerSpongeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mengerSpongeFromEventFlow (mengerSpongeToEventFlow x) = some x
    exact mengerSponge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mengerSpongeToEventFlow_injective heq)

theorem MengerSpongeTasteGate_single_carrier_alignment :
    ChapterTasteGate MengerSpongeUp ∧
      ∃ sample : MengerSpongeUp,
        mengerSpongeFields sample =
          [BHist.e0 BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact mengerSpongeChapterTasteGate
  · exact
      ⟨MengerSpongeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty, rfl⟩

end BEDC.Derived.MengerSpongeUp
