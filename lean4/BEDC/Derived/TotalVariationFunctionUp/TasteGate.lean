import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotalVariationFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotalVariationFunctionUp : Type where
  | mk (B L J X D G S I H C P N : BHist) : TotalVariationFunctionUp
  deriving DecidableEq

def totalVariationFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totalVariationFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totalVariationFunctionEncodeBHist h

def totalVariationFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totalVariationFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totalVariationFunctionDecodeBHist tail)

private theorem totalVariationFunction_decode_encode_bhist :
    ∀ h : BHist, totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def totalVariationFunctionFields : TotalVariationFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TotalVariationFunctionUp.mk B L J X D G S I H C P N =>
      [B, L, J, X, D, G, S, I, H, C, P, N]

def totalVariationFunctionToEventFlow : TotalVariationFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (totalVariationFunctionFields x).map totalVariationFunctionEncodeBHist

private def totalVariationFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => totalVariationFunctionEventAt index rest

def totalVariationFunctionFromEventFlow (flow : EventFlow) : Option TotalVariationFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TotalVariationFunctionUp.mk
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 0 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 1 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 2 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 3 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 4 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 5 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 6 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 7 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 8 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 9 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 10 flow))
      (totalVariationFunctionDecodeBHist (totalVariationFunctionEventAt 11 flow)))

private theorem totalVariationFunction_round_trip :
    ∀ x : TotalVariationFunctionUp,
      totalVariationFunctionFromEventFlow (totalVariationFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L J X D G S I H C P N =>
      change
        some
          (TotalVariationFunctionUp.mk
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist B))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist L))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist J))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist X))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist D))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist G))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist S))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist I))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist H))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist C))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist P))
            (totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist N))) =
          some (TotalVariationFunctionUp.mk B L J X D G S I H C P N)
      rw [totalVariationFunction_decode_encode_bhist B,
        totalVariationFunction_decode_encode_bhist L,
        totalVariationFunction_decode_encode_bhist J,
        totalVariationFunction_decode_encode_bhist X,
        totalVariationFunction_decode_encode_bhist D,
        totalVariationFunction_decode_encode_bhist G,
        totalVariationFunction_decode_encode_bhist S,
        totalVariationFunction_decode_encode_bhist I,
        totalVariationFunction_decode_encode_bhist H,
        totalVariationFunction_decode_encode_bhist C,
        totalVariationFunction_decode_encode_bhist P,
        totalVariationFunction_decode_encode_bhist N]

private theorem totalVariationFunctionToEventFlow_injective {x y : TotalVariationFunctionUp} :
    totalVariationFunctionToEventFlow x = totalVariationFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totalVariationFunctionFromEventFlow (totalVariationFunctionToEventFlow x) =
        totalVariationFunctionFromEventFlow (totalVariationFunctionToEventFlow y) :=
    congrArg totalVariationFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (totalVariationFunction_round_trip x).symm
      (Eq.trans hread (totalVariationFunction_round_trip y)))

instance totalVariationFunctionBHistCarrier : BHistCarrier TotalVariationFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totalVariationFunctionToEventFlow
  fromEventFlow := totalVariationFunctionFromEventFlow

instance totalVariationFunctionChapterTasteGate : ChapterTasteGate TotalVariationFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totalVariationFunctionFromEventFlow (totalVariationFunctionToEventFlow x) = some x
    exact totalVariationFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (totalVariationFunctionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TotalVariationFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  totalVariationFunctionChapterTasteGate

theorem TotalVariationFunctionTasteGate_single_carrier_alignment :
    (forall h : BHist, totalVariationFunctionDecodeBHist (totalVariationFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier TotalVariationFunctionUp) ∧
        Nonempty (ChapterTasteGate TotalVariationFunctionUp) ∧
          totalVariationFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact totalVariationFunction_decode_encode_bhist
  · constructor
    · exact ⟨totalVariationFunctionBHistCarrier⟩
    · constructor
      · exact ⟨totalVariationFunctionChapterTasteGate⟩
      · rfl

end BEDC.Derived.TotalVariationFunctionUp
