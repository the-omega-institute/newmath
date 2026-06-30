import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VariationDiminishingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VariationDiminishingUp : Type where
  | mk (B T R I K M H C P N : BHist) : VariationDiminishingUp
  deriving DecidableEq

def variationDiminishingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: variationDiminishingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: variationDiminishingEncodeBHist h

def variationDiminishingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (variationDiminishingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (variationDiminishingDecodeBHist tail)

private theorem variationDiminishingDecode_encode_bhist :
    ∀ h : BHist,
      variationDiminishingDecodeBHist (variationDiminishingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def variationDiminishingFields : VariationDiminishingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VariationDiminishingUp.mk B T R I K M H C P N => [B, T, R, I, K, M, H, C, P, N]

def variationDiminishingToEventFlow : VariationDiminishingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (variationDiminishingFields x).map variationDiminishingEncodeBHist

private def variationDiminishingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => variationDiminishingEventAt index rest

def variationDiminishingFromEventFlow
    (ef : EventFlow) : Option VariationDiminishingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (VariationDiminishingUp.mk
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 0 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 1 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 2 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 3 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 4 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 5 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 6 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 7 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 8 ef))
      (variationDiminishingDecodeBHist (variationDiminishingEventAt 9 ef)))

private theorem variationDiminishing_round_trip
    (x : VariationDiminishingUp) :
    variationDiminishingFromEventFlow (variationDiminishingToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B T R I K M H C P N =>
      change
        some
          (VariationDiminishingUp.mk
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist B))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist T))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist R))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist I))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist K))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist M))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist H))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist C))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist P))
            (variationDiminishingDecodeBHist (variationDiminishingEncodeBHist N))) =
          some (VariationDiminishingUp.mk B T R I K M H C P N)
      rw [variationDiminishingDecode_encode_bhist B,
        variationDiminishingDecode_encode_bhist T,
        variationDiminishingDecode_encode_bhist R,
        variationDiminishingDecode_encode_bhist I,
        variationDiminishingDecode_encode_bhist K,
        variationDiminishingDecode_encode_bhist M,
        variationDiminishingDecode_encode_bhist H,
        variationDiminishingDecode_encode_bhist C,
        variationDiminishingDecode_encode_bhist P,
        variationDiminishingDecode_encode_bhist N]

private theorem variationDiminishingToEventFlow_injective
    {x y : VariationDiminishingUp} :
    variationDiminishingToEventFlow x = variationDiminishingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      variationDiminishingFromEventFlow (variationDiminishingToEventFlow x) =
        variationDiminishingFromEventFlow (variationDiminishingToEventFlow y) :=
    congrArg variationDiminishingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (variationDiminishing_round_trip x).symm
      (Eq.trans hread (variationDiminishing_round_trip y)))

instance variationDiminishingBHistCarrier :
    BHistCarrier VariationDiminishingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := variationDiminishingToEventFlow
  fromEventFlow := variationDiminishingFromEventFlow

instance variationDiminishingChapterTasteGate :
    ChapterTasteGate VariationDiminishingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change variationDiminishingFromEventFlow (variationDiminishingToEventFlow x) = some x
    exact variationDiminishing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (variationDiminishingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate VariationDiminishingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  variationDiminishingChapterTasteGate

theorem VariationDiminishingTasteGate_single_carrier_alignment :
    (∀ h : BHist, variationDiminishingDecodeBHist (variationDiminishingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VariationDiminishingUp) ∧
        Nonempty (ChapterTasteGate VariationDiminishingUp) ∧
          variationDiminishingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact variationDiminishingDecode_encode_bhist
  · constructor
    · exact ⟨variationDiminishingBHistCarrier⟩
    · constructor
      · exact ⟨variationDiminishingChapterTasteGate⟩
      · rfl

end BEDC.Derived.VariationDiminishingUp
