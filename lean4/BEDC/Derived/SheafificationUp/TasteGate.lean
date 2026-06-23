import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SheafificationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SheafificationUp : Type where
  | mk (C T J P L G S H R Q N : BHist) : SheafificationUp
  deriving DecidableEq

def sheafificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sheafificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sheafificationEncodeBHist h

def sheafificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sheafificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sheafificationDecodeBHist tail)

private theorem sheafificationDecode_encode :
    ∀ h : BHist, sheafificationDecodeBHist (sheafificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sheafificationFields : SheafificationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SheafificationUp.mk C T J P L G S H R Q N => [C, T, J, P, L, G, S, H, R, Q, N]

def sheafificationToEventFlow : SheafificationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sheafificationFields x).map sheafificationEncodeBHist

private def sheafificationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sheafificationEventAt index rest

def sheafificationFromEventFlow (ef : EventFlow) : Option SheafificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SheafificationUp.mk
      (sheafificationDecodeBHist (sheafificationEventAt 0 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 1 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 2 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 3 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 4 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 5 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 6 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 7 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 8 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 9 ef))
      (sheafificationDecodeBHist (sheafificationEventAt 10 ef)))

private theorem sheafification_round_trip :
    ∀ x : SheafificationUp,
      sheafificationFromEventFlow (sheafificationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C T J P L G S H R Q N =>
      change
        some
          (SheafificationUp.mk
            (sheafificationDecodeBHist (sheafificationEncodeBHist C))
            (sheafificationDecodeBHist (sheafificationEncodeBHist T))
            (sheafificationDecodeBHist (sheafificationEncodeBHist J))
            (sheafificationDecodeBHist (sheafificationEncodeBHist P))
            (sheafificationDecodeBHist (sheafificationEncodeBHist L))
            (sheafificationDecodeBHist (sheafificationEncodeBHist G))
            (sheafificationDecodeBHist (sheafificationEncodeBHist S))
            (sheafificationDecodeBHist (sheafificationEncodeBHist H))
            (sheafificationDecodeBHist (sheafificationEncodeBHist R))
            (sheafificationDecodeBHist (sheafificationEncodeBHist Q))
            (sheafificationDecodeBHist (sheafificationEncodeBHist N))) =
          some (SheafificationUp.mk C T J P L G S H R Q N)
      rw [sheafificationDecode_encode C, sheafificationDecode_encode T,
        sheafificationDecode_encode J, sheafificationDecode_encode P,
        sheafificationDecode_encode L, sheafificationDecode_encode G,
        sheafificationDecode_encode S, sheafificationDecode_encode H,
        sheafificationDecode_encode R, sheafificationDecode_encode Q,
        sheafificationDecode_encode N]

private theorem sheafificationToEventFlow_injective {x y : SheafificationUp} :
    sheafificationToEventFlow x = sheafificationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sheafificationFromEventFlow (sheafificationToEventFlow x) =
        sheafificationFromEventFlow (sheafificationToEventFlow y) :=
    congrArg sheafificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sheafification_round_trip x).symm
      (Eq.trans hread (sheafification_round_trip y)))

instance sheafificationBHistCarrier : BHistCarrier SheafificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sheafificationToEventFlow
  fromEventFlow := sheafificationFromEventFlow

instance sheafificationChapterTasteGate : ChapterTasteGate SheafificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sheafificationFromEventFlow (sheafificationToEventFlow x) = some x
    exact sheafification_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sheafificationToEventFlow_injective heq)

theorem SheafificationTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SheafificationUp) ∧
      Nonempty (ChapterTasteGate SheafificationUp) ∧
        (∀ h : BHist, sheafificationDecodeBHist (sheafificationEncodeBHist h) = h) ∧
          (∀ x : SheafificationUp,
            sheafificationFromEventFlow (sheafificationToEventFlow x) = some x) ∧
            sheafificationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨sheafificationBHistCarrier⟩,
      ⟨sheafificationChapterTasteGate⟩,
      sheafificationDecode_encode,
      sheafification_round_trip,
      rfl⟩

end BEDC.Derived.SheafificationUp.TasteGate
