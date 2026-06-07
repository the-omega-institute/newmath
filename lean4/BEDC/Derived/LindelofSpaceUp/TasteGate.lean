import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LindelofSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LindelofSpaceCarrier : Type where
  | mk (X T B U S R H C P N : BHist) : LindelofSpaceCarrier
  deriving DecidableEq

def lindelofSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lindelofSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lindelofSpaceEncodeBHist h

def lindelofSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lindelofSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lindelofSpaceDecodeBHist tail)

private theorem lindelofSpace_decode_encode :
    ∀ h : BHist, lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lindelofSpaceFields : LindelofSpaceCarrier → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LindelofSpaceCarrier.mk X T B U S R H C P N => [X, T, B, U, S, R, H, C, P, N]

def lindelofSpaceToEventFlow : LindelofSpaceCarrier → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lindelofSpaceFields x).map lindelofSpaceEncodeBHist

private def lindelofSpaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lindelofSpaceRawAt index rest

def lindelofSpaceFromEventFlow (flow : EventFlow) : Option LindelofSpaceCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LindelofSpaceCarrier.mk
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 0 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 1 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 2 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 3 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 4 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 5 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 6 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 7 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 8 flow))
      (lindelofSpaceDecodeBHist (lindelofSpaceRawAt 9 flow)))

private theorem lindelofSpace_round_trip :
    ∀ x : LindelofSpaceCarrier,
      lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T B U S R H C P N =>
      change
        some
          (LindelofSpaceCarrier.mk
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist X))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist T))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist B))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist U))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist S))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist R))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist H))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist C))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist P))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist N))) =
          some (LindelofSpaceCarrier.mk X T B U S R H C P N)
      rw [lindelofSpace_decode_encode X,
        lindelofSpace_decode_encode T,
        lindelofSpace_decode_encode B,
        lindelofSpace_decode_encode U,
        lindelofSpace_decode_encode S,
        lindelofSpace_decode_encode R,
        lindelofSpace_decode_encode H,
        lindelofSpace_decode_encode C,
        lindelofSpace_decode_encode P,
        lindelofSpace_decode_encode N]

private theorem lindelofSpaceToEventFlow_injective {x y : LindelofSpaceCarrier} :
    lindelofSpaceToEventFlow x = lindelofSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow x) =
        lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow y) :=
    congrArg lindelofSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lindelofSpace_round_trip x).symm
      (Eq.trans hread (lindelofSpace_round_trip y)))

instance lindelofSpaceBHistCarrier : BHistCarrier LindelofSpaceCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lindelofSpaceToEventFlow
  fromEventFlow := lindelofSpaceFromEventFlow

instance lindelofSpaceChapterTasteGate : ChapterTasteGate LindelofSpaceCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow x) = some x
    exact lindelofSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lindelofSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LindelofSpaceCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  lindelofSpaceChapterTasteGate

end BEDC.Derived.LindelofSpaceUp
