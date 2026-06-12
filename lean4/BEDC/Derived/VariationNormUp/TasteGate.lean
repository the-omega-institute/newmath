import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VariationNormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VariationNormUp : Type where
  | mk (B R Q S D A H C P N : BHist) : VariationNormUp
  deriving DecidableEq

def variationNormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: variationNormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: variationNormEncodeBHist h

def variationNormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (variationNormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (variationNormDecodeBHist tail)

private theorem variationNorm_decode_encode_bhist :
    ∀ h : BHist, variationNormDecodeBHist (variationNormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def variationNormFields : VariationNormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VariationNormUp.mk B R Q S D A H C P N => [B, R, Q, S, D, A, H, C, P, N]

def variationNormToEventFlow : VariationNormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (variationNormFields x).map variationNormEncodeBHist

private def variationNormEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => variationNormEventAt index rest

def variationNormFromEventFlow (flow : EventFlow) : Option VariationNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (VariationNormUp.mk
      (variationNormDecodeBHist (variationNormEventAt 0 flow))
      (variationNormDecodeBHist (variationNormEventAt 1 flow))
      (variationNormDecodeBHist (variationNormEventAt 2 flow))
      (variationNormDecodeBHist (variationNormEventAt 3 flow))
      (variationNormDecodeBHist (variationNormEventAt 4 flow))
      (variationNormDecodeBHist (variationNormEventAt 5 flow))
      (variationNormDecodeBHist (variationNormEventAt 6 flow))
      (variationNormDecodeBHist (variationNormEventAt 7 flow))
      (variationNormDecodeBHist (variationNormEventAt 8 flow))
      (variationNormDecodeBHist (variationNormEventAt 9 flow)))

private theorem variationNorm_round_trip :
    ∀ x : VariationNormUp,
      variationNormFromEventFlow (variationNormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B R Q S D A H C P N =>
      change
        some
          (VariationNormUp.mk
            (variationNormDecodeBHist (variationNormEncodeBHist B))
            (variationNormDecodeBHist (variationNormEncodeBHist R))
            (variationNormDecodeBHist (variationNormEncodeBHist Q))
            (variationNormDecodeBHist (variationNormEncodeBHist S))
            (variationNormDecodeBHist (variationNormEncodeBHist D))
            (variationNormDecodeBHist (variationNormEncodeBHist A))
            (variationNormDecodeBHist (variationNormEncodeBHist H))
            (variationNormDecodeBHist (variationNormEncodeBHist C))
            (variationNormDecodeBHist (variationNormEncodeBHist P))
            (variationNormDecodeBHist (variationNormEncodeBHist N))) =
          some (VariationNormUp.mk B R Q S D A H C P N)
      rw [variationNorm_decode_encode_bhist B, variationNorm_decode_encode_bhist R,
        variationNorm_decode_encode_bhist Q, variationNorm_decode_encode_bhist S,
        variationNorm_decode_encode_bhist D, variationNorm_decode_encode_bhist A,
        variationNorm_decode_encode_bhist H, variationNorm_decode_encode_bhist C,
        variationNorm_decode_encode_bhist P, variationNorm_decode_encode_bhist N]

private theorem variationNormToEventFlow_injective {x y : VariationNormUp} :
    variationNormToEventFlow x = variationNormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      variationNormFromEventFlow (variationNormToEventFlow x) =
        variationNormFromEventFlow (variationNormToEventFlow y) :=
    congrArg variationNormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (variationNorm_round_trip x).symm
      (Eq.trans hread (variationNorm_round_trip y)))

instance variationNormBHistCarrier : BHistCarrier VariationNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := variationNormToEventFlow
  fromEventFlow := variationNormFromEventFlow

instance variationNormChapterTasteGate : ChapterTasteGate VariationNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change variationNormFromEventFlow (variationNormToEventFlow x) = some x
    exact variationNorm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (variationNormToEventFlow_injective heq)

theorem VariationNormTasteGate_single_carrier_alignment :
    (∀ h : BHist, variationNormDecodeBHist (variationNormEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VariationNormUp) ∧ Nonempty (ChapterTasteGate VariationNormUp) ∧
        variationNormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact variationNorm_decode_encode_bhist
  · constructor
    · exact ⟨variationNormBHistCarrier⟩
    · constructor
      · exact ⟨variationNormChapterTasteGate⟩
      · rfl

end BEDC.Derived.VariationNormUp
