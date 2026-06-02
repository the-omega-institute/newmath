import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwartzFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwartzFunctionUp : Type where
  | mk (D W G F T R L H C P N : BHist) : SchwartzFunctionUp
  deriving DecidableEq

def schwartzFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwartzFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwartzFunctionEncodeBHist h

def schwartzFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwartzFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwartzFunctionDecodeBHist tail)

private theorem schwartzFunction_decode_encode_bhist :
    ∀ h : BHist, schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schwartzFunctionFields : SchwartzFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwartzFunctionUp.mk D W G F T R L H C P N => [D, W, G, F, T, R, L, H, C, P, N]

def schwartzFunctionToEventFlow : SchwartzFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map schwartzFunctionEncodeBHist (schwartzFunctionFields x)

private def schwartzFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schwartzFunctionEventAt index rest

def schwartzFunctionFromEventFlow : EventFlow → Option SchwartzFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (SchwartzFunctionUp.mk
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 0 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 1 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 2 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 3 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 4 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 5 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 6 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 7 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 8 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 9 flow))
        (schwartzFunctionDecodeBHist (schwartzFunctionEventAt 10 flow)))

private theorem schwartzFunction_round_trip :
    ∀ x : SchwartzFunctionUp,
      schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W G F T R L H C P N =>
      change
        some
            (SchwartzFunctionUp.mk
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist D))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist W))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist G))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist F))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist T))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist R))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist L))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist H))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist C))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist P))
              (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist N))) =
          some (SchwartzFunctionUp.mk D W G F T R L H C P N)
      rw [schwartzFunction_decode_encode_bhist D,
        schwartzFunction_decode_encode_bhist W,
        schwartzFunction_decode_encode_bhist G,
        schwartzFunction_decode_encode_bhist F,
        schwartzFunction_decode_encode_bhist T,
        schwartzFunction_decode_encode_bhist R,
        schwartzFunction_decode_encode_bhist L,
        schwartzFunction_decode_encode_bhist H,
        schwartzFunction_decode_encode_bhist C,
        schwartzFunction_decode_encode_bhist P,
        schwartzFunction_decode_encode_bhist N]

private theorem schwartzFunctionToEventFlow_injective {x y : SchwartzFunctionUp} :
    schwartzFunctionToEventFlow x = schwartzFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow x) =
        schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow y) :=
    congrArg schwartzFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (schwartzFunction_round_trip x).symm
      (Eq.trans hread (schwartzFunction_round_trip y)))

instance schwartzFunctionBHistCarrier : BHistCarrier SchwartzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwartzFunctionToEventFlow
  fromEventFlow := schwartzFunctionFromEventFlow

instance schwartzFunctionChapterTasteGate : ChapterTasteGate SchwartzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow x) = some x
    exact schwartzFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (schwartzFunctionToEventFlow_injective heq)

theorem SchwartzFunctionTasteGate_single_carrier_alignment :
    (forall h : BHist, schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SchwartzFunctionUp) ∧
        Nonempty (ChapterTasteGate SchwartzFunctionUp) ∧
          schwartzFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨schwartzFunction_decode_encode_bhist,
      ⟨schwartzFunctionBHistCarrier⟩,
      ⟨schwartzFunctionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SchwartzFunctionUp
