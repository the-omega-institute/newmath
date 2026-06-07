import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArzelaAscoliSelectionUp.TasteGate

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

private theorem arzelaAscoliSelection_decode_encode :
    ∀ h : BHist,
      arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def arzelaAscoliSelectionFields :
    ArzelaAscoliSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArzelaAscoliSelectionUp.mk X E B D M Q R H C P N => [X, E, B, D, M, Q, R, H, C, P, N]

def arzelaAscoliSelectionToEventFlow :
    ArzelaAscoliSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map arzelaAscoliSelectionEncodeBHist (arzelaAscoliSelectionFields x)

private def arzelaAscoliSelectionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => arzelaAscoliSelectionRawAt index rest

def arzelaAscoliSelectionFromEventFlow
    (flow : EventFlow) : Option ArzelaAscoliSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArzelaAscoliSelectionUp.mk
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 0 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 1 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 2 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 3 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 4 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 5 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 6 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 7 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 8 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 9 flow))
      (arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionRawAt 10 flow)))

private theorem arzelaAscoliSelection_round_trip :
    ∀ x : ArzelaAscoliSelectionUp,
      arzelaAscoliSelectionFromEventFlow (arzelaAscoliSelectionToEventFlow x) = some x := by
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
      rw [arzelaAscoliSelection_decode_encode X,
        arzelaAscoliSelection_decode_encode E,
        arzelaAscoliSelection_decode_encode B,
        arzelaAscoliSelection_decode_encode D,
        arzelaAscoliSelection_decode_encode M,
        arzelaAscoliSelection_decode_encode Q,
        arzelaAscoliSelection_decode_encode R,
        arzelaAscoliSelection_decode_encode H,
        arzelaAscoliSelection_decode_encode C,
        arzelaAscoliSelection_decode_encode P,
        arzelaAscoliSelection_decode_encode N]

private theorem arzelaAscoliSelectionToEventFlow_injective
    {x y : ArzelaAscoliSelectionUp} :
    arzelaAscoliSelectionToEventFlow x = arzelaAscoliSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arzelaAscoliSelectionFromEventFlow (arzelaAscoliSelectionToEventFlow x) =
        arzelaAscoliSelectionFromEventFlow (arzelaAscoliSelectionToEventFlow y) :=
    congrArg arzelaAscoliSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (arzelaAscoliSelection_round_trip x).symm
      (Eq.trans hread (arzelaAscoliSelection_round_trip y)))

instance arzelaAscoliSelectionBHistCarrier : BHistCarrier ArzelaAscoliSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arzelaAscoliSelectionToEventFlow
  fromEventFlow := arzelaAscoliSelectionFromEventFlow

instance arzelaAscoliSelectionChapterTasteGate :
    ChapterTasteGate ArzelaAscoliSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      arzelaAscoliSelectionFromEventFlow (arzelaAscoliSelectionToEventFlow x) = some x
    exact arzelaAscoliSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (arzelaAscoliSelectionToEventFlow_injective heq)

instance arzelaAscoliSelectionFieldFaithful :
    FieldFaithful ArzelaAscoliSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := arzelaAscoliSelectionFields
  field_faithful := by
    intro x y h
    cases x with
    | mk X1 E1 B1 D1 M1 Q1 R1 H1 C1 P1 N1 =>
        cases y with
        | mk X2 E2 B2 D2 M2 Q2 R2 H2 C2 P2 N2 =>
            cases h
            rfl

def taste_gate : ChapterTasteGate ArzelaAscoliSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  arzelaAscoliSelectionChapterTasteGate

theorem ArzelaAscoliSelectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ArzelaAscoliSelectionUp) ∧
      Nonempty (FieldFaithful ArzelaAscoliSelectionUp) ∧
        (∀ h : BHist,
          arzelaAscoliSelectionDecodeBHist (arzelaAscoliSelectionEncodeBHist h) = h) ∧
          (∀ x : ArzelaAscoliSelectionUp,
            arzelaAscoliSelectionFromEventFlow (arzelaAscoliSelectionToEventFlow x) =
              some x) ∧
            (∀ x y : ArzelaAscoliSelectionUp,
              arzelaAscoliSelectionToEventFlow x = arzelaAscoliSelectionToEventFlow y →
                x = y) ∧
              arzelaAscoliSelectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨arzelaAscoliSelectionChapterTasteGate⟩,
      ⟨arzelaAscoliSelectionFieldFaithful⟩,
      arzelaAscoliSelection_decode_encode,
      arzelaAscoliSelection_round_trip,
      by
        intro x y heq
        exact arzelaAscoliSelectionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ArzelaAscoliSelectionUp.TasteGate
