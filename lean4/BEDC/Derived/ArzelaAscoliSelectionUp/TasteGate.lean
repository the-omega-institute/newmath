import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArzelaAscoliSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArzelaAscoliSelectionUp : Type where
  | mk (X E B D M Q R H C P N : BHist) : ArzelaAscoliSelectionUp
  deriving DecidableEq

def arzelaAscoliSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arzelaAscoliSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arzelaAscoliSelectionEncodeBHist h

def arzelaAscoliSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arzelaAscoliSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arzelaAscoliSelectionDecodeBHist tail)

private theorem arzelaAscoliSelection_decode_encode_bhist :
    ∀ h : BHist,
      arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def arzelaAscoliSelectionFields : ArzelaAscoliSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArzelaAscoliSelectionUp.mk X E B D M Q R H C P N =>
      [X, E, B, D, M, Q, R, H, C, P, N]

def arzelaAscoliSelectionToEventFlow : ArzelaAscoliSelectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (arzelaAscoliSelectionFields x).map arzelaAscoliSelectionEncodeBHist

private def arzelaAscoliSelectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => arzelaAscoliSelectionEventAtDefault index rest

def arzelaAscoliSelectionFromEventFlow
    (flow : EventFlow) : Option ArzelaAscoliSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArzelaAscoliSelectionUp.mk
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 0 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 1 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 2 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 3 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 4 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 5 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 6 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 7 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 8 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 9 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEventAtDefault 10 flow)))

private theorem arzelaAscoliSelection_round_trip :
    ∀ x : ArzelaAscoliSelectionUp,
      arzelaAscoliSelectionFromEventFlow
        (arzelaAscoliSelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X E B D M Q R H C P N =>
      change
        some
          (ArzelaAscoliSelectionUp.mk
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist X))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist E))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist B))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist D))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist M))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist Q))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist R))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist H))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist C))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist P))
            (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist N))) =
          some (ArzelaAscoliSelectionUp.mk X E B D M Q R H C P N)
      rw [arzelaAscoliSelection_decode_encode_bhist X,
        arzelaAscoliSelection_decode_encode_bhist E,
        arzelaAscoliSelection_decode_encode_bhist B,
        arzelaAscoliSelection_decode_encode_bhist D,
        arzelaAscoliSelection_decode_encode_bhist M,
        arzelaAscoliSelection_decode_encode_bhist Q,
        arzelaAscoliSelection_decode_encode_bhist R,
        arzelaAscoliSelection_decode_encode_bhist H,
        arzelaAscoliSelection_decode_encode_bhist C,
        arzelaAscoliSelection_decode_encode_bhist P,
        arzelaAscoliSelection_decode_encode_bhist N]

private theorem arzelaAscoliSelectionToEventFlow_injective
    {x y : ArzelaAscoliSelectionUp} :
    arzelaAscoliSelectionToEventFlow x = arzelaAscoliSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arzelaAscoliSelectionFromEventFlow (arzelaAscoliSelectionToEventFlow x) =
        arzelaAscoliSelectionFromEventFlow (arzelaAscoliSelectionToEventFlow y) :=
    congrArg arzelaAscoliSelectionFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (arzelaAscoliSelection_round_trip x).symm
        (Eq.trans hread (arzelaAscoliSelection_round_trip y)))

instance arzelaAscoliSelectionBHistCarrier :
    BHistCarrier ArzelaAscoliSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arzelaAscoliSelectionToEventFlow
  fromEventFlow := arzelaAscoliSelectionFromEventFlow

instance arzelaAscoliSelectionChapterTasteGate :
    ChapterTasteGate ArzelaAscoliSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      arzelaAscoliSelectionFromEventFlow
        (arzelaAscoliSelectionToEventFlow x) = some x
    exact arzelaAscoliSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (arzelaAscoliSelectionToEventFlow_injective heq)

theorem ArzelaAscoliSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ArzelaAscoliSelectionUp) ∧
        Nonempty (ChapterTasteGate ArzelaAscoliSelectionUp) ∧
          arzelaAscoliSelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨arzelaAscoliSelection_decode_encode_bhist,
      ⟨arzelaAscoliSelectionBHistCarrier⟩,
      ⟨arzelaAscoliSelectionChapterTasteGate⟩,
      rfl⟩

namespace TasteGate

theorem ArzelaAscoliSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ArzelaAscoliSelectionUp) ∧
        Nonempty (ChapterTasteGate ArzelaAscoliSelectionUp) ∧
          arzelaAscoliSelectionEncodeBHist BHist.Empty = ([] : List BMark) :=
  BEDC.Derived.ArzelaAscoliSelectionUp.ArzelaAscoliSelectionTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.ArzelaAscoliSelectionUp
