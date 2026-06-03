import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompleteApartnessSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompleteApartnessSpaceUp : Type where
  | mk (X G T S R D E L Q H C P N : BHist) : CauchyCompleteApartnessSpaceUp
  deriving DecidableEq

def cauchyCompleteApartnessSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompleteApartnessSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompleteApartnessSpaceEncodeBHist h

def cauchyCompleteApartnessSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompleteApartnessSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompleteApartnessSpaceDecodeBHist tail)

private theorem cauchyCompleteApartnessSpace_decode_encode_bhist :
    ∀ h : BHist,
      cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompleteApartnessSpaceToEventFlow :
    CauchyCompleteApartnessSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompleteApartnessSpaceUp.mk X G T S R D E L Q H C P N =>
      [cauchyCompleteApartnessSpaceEncodeBHist X,
        cauchyCompleteApartnessSpaceEncodeBHist G,
        cauchyCompleteApartnessSpaceEncodeBHist T,
        cauchyCompleteApartnessSpaceEncodeBHist S,
        cauchyCompleteApartnessSpaceEncodeBHist R,
        cauchyCompleteApartnessSpaceEncodeBHist D,
        cauchyCompleteApartnessSpaceEncodeBHist E,
        cauchyCompleteApartnessSpaceEncodeBHist L,
        cauchyCompleteApartnessSpaceEncodeBHist Q,
        cauchyCompleteApartnessSpaceEncodeBHist H,
        cauchyCompleteApartnessSpaceEncodeBHist C,
        cauchyCompleteApartnessSpaceEncodeBHist P,
        cauchyCompleteApartnessSpaceEncodeBHist N]

private def cauchyCompleteApartnessSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompleteApartnessSpaceEventAtDefault index rest

def cauchyCompleteApartnessSpaceFromEventFlow
    (ef : EventFlow) : Option CauchyCompleteApartnessSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompleteApartnessSpaceUp.mk
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 0 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 1 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 2 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 3 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 4 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 5 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 6 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 7 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 8 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 9 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 10 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 11 ef))
      (cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEventAtDefault 12 ef)))

private theorem cauchyCompleteApartnessSpace_round_trip :
    ∀ x : CauchyCompleteApartnessSpaceUp,
      cauchyCompleteApartnessSpaceFromEventFlow
        (cauchyCompleteApartnessSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X G T S R D E L Q H C P N =>
      change
        some
          (CauchyCompleteApartnessSpaceUp.mk
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist X))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist G))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist T))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist S))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist R))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist D))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist E))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist L))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist Q))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist H))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist C))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist P))
            (cauchyCompleteApartnessSpaceDecodeBHist
              (cauchyCompleteApartnessSpaceEncodeBHist N))) =
          some (CauchyCompleteApartnessSpaceUp.mk X G T S R D E L Q H C P N)
      rw [cauchyCompleteApartnessSpace_decode_encode_bhist X,
        cauchyCompleteApartnessSpace_decode_encode_bhist G,
        cauchyCompleteApartnessSpace_decode_encode_bhist T,
        cauchyCompleteApartnessSpace_decode_encode_bhist S,
        cauchyCompleteApartnessSpace_decode_encode_bhist R,
        cauchyCompleteApartnessSpace_decode_encode_bhist D,
        cauchyCompleteApartnessSpace_decode_encode_bhist E,
        cauchyCompleteApartnessSpace_decode_encode_bhist L,
        cauchyCompleteApartnessSpace_decode_encode_bhist Q,
        cauchyCompleteApartnessSpace_decode_encode_bhist H,
        cauchyCompleteApartnessSpace_decode_encode_bhist C,
        cauchyCompleteApartnessSpace_decode_encode_bhist P,
        cauchyCompleteApartnessSpace_decode_encode_bhist N]

private theorem cauchyCompleteApartnessSpaceToEventFlow_injective
    {x y : CauchyCompleteApartnessSpaceUp} :
    cauchyCompleteApartnessSpaceToEventFlow x =
      cauchyCompleteApartnessSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompleteApartnessSpaceFromEventFlow
          (cauchyCompleteApartnessSpaceToEventFlow x) =
        cauchyCompleteApartnessSpaceFromEventFlow
          (cauchyCompleteApartnessSpaceToEventFlow y) :=
    congrArg cauchyCompleteApartnessSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompleteApartnessSpace_round_trip x).symm
      (Eq.trans hread (cauchyCompleteApartnessSpace_round_trip y)))

instance cauchyCompleteApartnessSpaceBHistCarrier :
    BHistCarrier CauchyCompleteApartnessSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompleteApartnessSpaceToEventFlow
  fromEventFlow := cauchyCompleteApartnessSpaceFromEventFlow

instance cauchyCompleteApartnessSpaceChapterTasteGate :
    ChapterTasteGate CauchyCompleteApartnessSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompleteApartnessSpaceFromEventFlow
        (cauchyCompleteApartnessSpaceToEventFlow x) = some x
    exact cauchyCompleteApartnessSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompleteApartnessSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompleteApartnessSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompleteApartnessSpaceChapterTasteGate

theorem CauchyCompleteApartnessSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompleteApartnessSpaceDecodeBHist
        (cauchyCompleteApartnessSpaceEncodeBHist h) = h) ∧
      (∀ x : CauchyCompleteApartnessSpaceUp,
        cauchyCompleteApartnessSpaceFromEventFlow
          (cauchyCompleteApartnessSpaceToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompleteApartnessSpaceUp,
          cauchyCompleteApartnessSpaceToEventFlow x =
            cauchyCompleteApartnessSpaceToEventFlow y → x = y) ∧
          cauchyCompleteApartnessSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyCompleteApartnessSpace_decode_encode_bhist
  · constructor
    · exact cauchyCompleteApartnessSpace_round_trip
    · constructor
      · intro x y heq
        exact cauchyCompleteApartnessSpaceToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyCompleteApartnessSpaceUp
