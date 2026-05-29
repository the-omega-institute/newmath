import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LandauSymbolUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LandauSymbolUp : Type where
  | mk (S T W B Q E H C P N : BHist) : LandauSymbolUp
  deriving DecidableEq

def landauSymbolEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: landauSymbolEncodeBHist h
  | BHist.e1 h => BMark.b1 :: landauSymbolEncodeBHist h

def landauSymbolDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (landauSymbolDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (landauSymbolDecodeBHist tail)

private theorem landauSymbol_decode_encode_bhist :
    ∀ h : BHist, landauSymbolDecodeBHist (landauSymbolEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def landauSymbolFields : LandauSymbolUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LandauSymbolUp.mk S T W B Q E H C P N => [S, T, W, B, Q, E, H, C, P, N]

def landauSymbolToEventFlow : LandauSymbolUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LandauSymbolUp.mk S T W B Q E H C P N =>
      [landauSymbolEncodeBHist S,
        landauSymbolEncodeBHist T,
        landauSymbolEncodeBHist W,
        landauSymbolEncodeBHist B,
        landauSymbolEncodeBHist Q,
        landauSymbolEncodeBHist E,
        landauSymbolEncodeBHist H,
        landauSymbolEncodeBHist C,
        landauSymbolEncodeBHist P,
        landauSymbolEncodeBHist N]

private def landauSymbolRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => landauSymbolRawAt n rest

private def landauSymbolLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => landauSymbolLengthEq n rest

def landauSymbolFromEventFlow : EventFlow → Option LandauSymbolUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match landauSymbolLengthEq 10 flow with
      | true =>
          some
            (LandauSymbolUp.mk
              (landauSymbolDecodeBHist (landauSymbolRawAt 0 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 1 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 2 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 3 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 4 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 5 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 6 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 7 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 8 flow))
              (landauSymbolDecodeBHist (landauSymbolRawAt 9 flow)))
      | false => none

private theorem landauSymbol_round_trip :
    ∀ x : LandauSymbolUp,
      landauSymbolFromEventFlow (landauSymbolToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W B Q E H C P N =>
      change
        some
          (LandauSymbolUp.mk
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist S))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist T))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist W))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist B))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist Q))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist E))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist H))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist C))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist P))
            (landauSymbolDecodeBHist (landauSymbolEncodeBHist N))) =
          some (LandauSymbolUp.mk S T W B Q E H C P N)
      rw [landauSymbol_decode_encode_bhist S,
        landauSymbol_decode_encode_bhist T,
        landauSymbol_decode_encode_bhist W,
        landauSymbol_decode_encode_bhist B,
        landauSymbol_decode_encode_bhist Q,
        landauSymbol_decode_encode_bhist E,
        landauSymbol_decode_encode_bhist H,
        landauSymbol_decode_encode_bhist C,
        landauSymbol_decode_encode_bhist P,
        landauSymbol_decode_encode_bhist N]

private theorem landauSymbolToEventFlow_injective {x y : LandauSymbolUp} :
    landauSymbolToEventFlow x = landauSymbolToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      landauSymbolFromEventFlow (landauSymbolToEventFlow x) =
        landauSymbolFromEventFlow (landauSymbolToEventFlow y) :=
    congrArg landauSymbolFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (landauSymbol_round_trip x).symm
      (Eq.trans hread (landauSymbol_round_trip y)))

instance landauSymbolBHistCarrier : BHistCarrier LandauSymbolUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := landauSymbolToEventFlow
  fromEventFlow := landauSymbolFromEventFlow

instance landauSymbolChapterTasteGate : ChapterTasteGate LandauSymbolUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change landauSymbolFromEventFlow (landauSymbolToEventFlow x) = some x
    exact landauSymbol_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (landauSymbolToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LandauSymbolUp :=
  -- BEDC touchpoint anchor: BHist BMark
  landauSymbolChapterTasteGate

theorem LandauSymbolTasteGate_single_carrier_alignment :
    (∀ h : BHist, landauSymbolDecodeBHist (landauSymbolEncodeBHist h) = h) ∧
      landauSymbolFields
          (LandauSymbolUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨landauSymbol_decode_encode_bhist, rfl⟩

end BEDC.Derived.LandauSymbolUp
