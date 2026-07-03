import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveIVPUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveIVPUp : Type where
  | mk (A M E B R S H C P N : BHist) : ConstructiveIVPUp
  deriving DecidableEq

def constructiveIVPEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveIVPEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveIVPEncodeBHist h

def constructiveIVPDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveIVPDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveIVPDecodeBHist tail)

private theorem constructiveIVPDecode_encode_bhist :
    ∀ h : BHist, constructiveIVPDecodeBHist (constructiveIVPEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveIVPFields : ConstructiveIVPUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveIVPUp.mk A M E B R S H C P N => [A, M, E, B, R, S, H, C, P, N]

def constructiveIVPToEventFlow : ConstructiveIVPUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (constructiveIVPFields x).map constructiveIVPEncodeBHist

private def constructiveIVPEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveIVPEventAtDefault index rest

def constructiveIVPFromEventFlow (ef : EventFlow) : Option ConstructiveIVPUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveIVPUp.mk
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 0 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 1 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 2 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 3 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 4 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 5 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 6 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 7 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 8 ef))
      (constructiveIVPDecodeBHist (constructiveIVPEventAtDefault 9 ef)))

private theorem constructiveIVP_round_trip :
    ∀ x : ConstructiveIVPUp,
      constructiveIVPFromEventFlow (constructiveIVPToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M E B R S H C P N =>
      change
        some
            (ConstructiveIVPUp.mk
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist A))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist M))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist E))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist B))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist R))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist S))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist H))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist C))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist P))
              (constructiveIVPDecodeBHist (constructiveIVPEncodeBHist N))) =
          some (ConstructiveIVPUp.mk A M E B R S H C P N)
      rw [constructiveIVPDecode_encode_bhist A, constructiveIVPDecode_encode_bhist M,
        constructiveIVPDecode_encode_bhist E, constructiveIVPDecode_encode_bhist B,
        constructiveIVPDecode_encode_bhist R, constructiveIVPDecode_encode_bhist S,
        constructiveIVPDecode_encode_bhist H, constructiveIVPDecode_encode_bhist C,
        constructiveIVPDecode_encode_bhist P, constructiveIVPDecode_encode_bhist N]

private theorem constructiveIVPToEventFlow_injective {x y : ConstructiveIVPUp} :
    constructiveIVPToEventFlow x = constructiveIVPToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveIVPFromEventFlow (constructiveIVPToEventFlow x) =
        constructiveIVPFromEventFlow (constructiveIVPToEventFlow y) :=
    congrArg constructiveIVPFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (constructiveIVP_round_trip x).symm
      (Eq.trans hread (constructiveIVP_round_trip y)))

instance constructiveIVPBHistCarrier : BHistCarrier ConstructiveIVPUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveIVPToEventFlow
  fromEventFlow := constructiveIVPFromEventFlow

instance constructiveIVPChapterTasteGate : ChapterTasteGate ConstructiveIVPUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveIVPFromEventFlow (constructiveIVPToEventFlow x) = some x
    exact constructiveIVP_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveIVPToEventFlow_injective heq)

theorem ConstructiveIVPTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveIVPDecodeBHist (constructiveIVPEncodeBHist h) = h) ∧
      (∀ x : ConstructiveIVPUp,
        constructiveIVPFromEventFlow (constructiveIVPToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveIVPUp,
          constructiveIVPToEventFlow x = constructiveIVPToEventFlow y → x = y) ∧
          constructiveIVPEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨constructiveIVPDecode_encode_bhist, constructiveIVP_round_trip,
      (fun _ _ heq => constructiveIVPToEventFlow_injective heq), rfl⟩

end BEDC.Derived.ConstructiveIVPUp
