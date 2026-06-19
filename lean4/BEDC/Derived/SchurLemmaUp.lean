import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchurLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchurLemmaUp : Type where
  | mk (U V H S T R P N : BHist) : SchurLemmaUp
  deriving DecidableEq

def schurLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schurLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schurLemmaEncodeBHist h

def schurLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schurLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schurLemmaDecodeBHist tail)

private theorem schurLemmaDecode_encode_bhist :
    ∀ h : BHist, schurLemmaDecodeBHist (schurLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schurLemmaFields : SchurLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchurLemmaUp.mk U V H S T R P N => [U, V, H, S, T, R, P, N]

def schurLemmaToEventFlow : SchurLemmaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (schurLemmaFields x).map schurLemmaEncodeBHist

private def schurLemmaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schurLemmaEventAtDefault index rest

def schurLemmaFromEventFlow (ef : EventFlow) : Option SchurLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SchurLemmaUp.mk
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 0 ef))
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 1 ef))
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 2 ef))
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 3 ef))
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 4 ef))
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 5 ef))
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 6 ef))
      (schurLemmaDecodeBHist (schurLemmaEventAtDefault 7 ef)))

private theorem schurLemma_round_trip :
    ∀ x : SchurLemmaUp,
      schurLemmaFromEventFlow (schurLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U V H S T R P N =>
      change
        some
          (SchurLemmaUp.mk
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist U))
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist V))
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist H))
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist S))
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist T))
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist R))
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist P))
            (schurLemmaDecodeBHist (schurLemmaEncodeBHist N))) =
          some (SchurLemmaUp.mk U V H S T R P N)
      rw [schurLemmaDecode_encode_bhist U, schurLemmaDecode_encode_bhist V,
        schurLemmaDecode_encode_bhist H, schurLemmaDecode_encode_bhist S,
        schurLemmaDecode_encode_bhist T, schurLemmaDecode_encode_bhist R,
        schurLemmaDecode_encode_bhist P, schurLemmaDecode_encode_bhist N]

private theorem SchurLemmaToEventFlow_injective {x y : SchurLemmaUp} :
    schurLemmaToEventFlow x = schurLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schurLemmaFromEventFlow (schurLemmaToEventFlow x) =
        schurLemmaFromEventFlow (schurLemmaToEventFlow y) :=
    congrArg schurLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (schurLemma_round_trip x).symm
      (Eq.trans hread (schurLemma_round_trip y)))

instance schurLemmaBHistCarrier : BHistCarrier SchurLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schurLemmaToEventFlow
  fromEventFlow := schurLemmaFromEventFlow

instance schurLemmaChapterTasteGate : ChapterTasteGate SchurLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schurLemmaFromEventFlow (schurLemmaToEventFlow x) = some x
    exact schurLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchurLemmaToEventFlow_injective heq)

theorem SchurLemmaTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SchurLemmaUp) ∧
      Nonempty (ChapterTasteGate SchurLemmaUp) ∧
        (∀ x : SchurLemmaUp, schurLemmaFromEventFlow (schurLemmaToEventFlow x) = some x) ∧
          (∀ x y : SchurLemmaUp,
            schurLemmaToEventFlow x = schurLemmaToEventFlow y → x = y) ∧
            schurLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨schurLemmaBHistCarrier⟩
  · constructor
    · exact ⟨schurLemmaChapterTasteGate⟩
    · constructor
      · exact schurLemma_round_trip
      · constructor
        · intro x y heq
          exact SchurLemmaToEventFlow_injective heq
        · rfl

end BEDC.Derived.SchurLemmaUp
