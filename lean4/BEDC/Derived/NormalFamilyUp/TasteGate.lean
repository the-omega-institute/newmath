import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalFamilyUp : Type where
  | mk (F X Y M E I Q H C P L : BHist) : NormalFamilyUp
  deriving DecidableEq

def normalFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalFamilyEncodeBHist h

def normalFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalFamilyDecodeBHist tail)

private theorem normalFamily_decode_encode_bhist :
    ∀ h : BHist, normalFamilyDecodeBHist (normalFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def normalFamilyFields : NormalFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalFamilyUp.mk F X Y M E I Q H C P L => [F, X, Y, M, E, I, Q, H, C, P, L]

def normalFamilyToEventFlow : NormalFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NormalFamilyUp.mk F X Y M E I Q H C P L =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        normalFamilyEncodeBHist F,
        normalFamilyEncodeBHist X,
        normalFamilyEncodeBHist Y,
        normalFamilyEncodeBHist M,
        normalFamilyEncodeBHist E,
        normalFamilyEncodeBHist I,
        normalFamilyEncodeBHist Q,
        normalFamilyEncodeBHist H,
        normalFamilyEncodeBHist C,
        normalFamilyEncodeBHist P,
        normalFamilyEncodeBHist L]

private def normalFamilyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => normalFamilyEventAtDefault index rest

def normalFamilyFromEventFlow : EventFlow → Option NormalFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (NormalFamilyUp.mk
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 1 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 2 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 3 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 4 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 5 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 6 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 7 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 8 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 9 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 10 ef))
        (normalFamilyDecodeBHist (normalFamilyEventAtDefault 11 ef)))

private theorem normalFamily_round_trip :
    ∀ x : NormalFamilyUp,
      normalFamilyFromEventFlow (normalFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F X Y M E I Q H C P L =>
      change
        some
          (NormalFamilyUp.mk
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist F))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist X))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist Y))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist M))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist E))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist I))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist Q))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist H))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist C))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist P))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist L))) =
          some (NormalFamilyUp.mk F X Y M E I Q H C P L)
      rw [normalFamily_decode_encode_bhist F, normalFamily_decode_encode_bhist X,
        normalFamily_decode_encode_bhist Y, normalFamily_decode_encode_bhist M,
        normalFamily_decode_encode_bhist E, normalFamily_decode_encode_bhist I,
        normalFamily_decode_encode_bhist Q, normalFamily_decode_encode_bhist H,
        normalFamily_decode_encode_bhist C, normalFamily_decode_encode_bhist P,
        normalFamily_decode_encode_bhist L]

private theorem normalFamilyToEventFlow_injective {x y : NormalFamilyUp} :
    normalFamilyToEventFlow x = normalFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalFamilyFromEventFlow (normalFamilyToEventFlow x) =
        normalFamilyFromEventFlow (normalFamilyToEventFlow y) :=
    congrArg normalFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (normalFamily_round_trip x).symm
      (Eq.trans hread (normalFamily_round_trip y)))

instance normalFamilyBHistCarrier : BHistCarrier NormalFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalFamilyToEventFlow
  fromEventFlow := normalFamilyFromEventFlow

instance normalFamilyChapterTasteGate : ChapterTasteGate NormalFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalFamilyFromEventFlow (normalFamilyToEventFlow x) = some x
    exact normalFamily_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (normalFamilyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NormalFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normalFamilyChapterTasteGate

theorem NormalFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist, normalFamilyDecodeBHist (normalFamilyEncodeBHist h) = h) ∧
      (∀ x : NormalFamilyUp,
        normalFamilyFromEventFlow (normalFamilyToEventFlow x) = some x) ∧
        normalFamilyFields
            (NormalFamilyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · intro x
    cases x with
    | mk F X Y M E I Q H C P L =>
        change
          some
            (NormalFamilyUp.mk
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist F))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist X))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist Y))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist M))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist E))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist I))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist Q))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist H))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist C))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist P))
              (normalFamilyDecodeBHist (normalFamilyEncodeBHist L))) =
            some (NormalFamilyUp.mk F X Y M E I Q H C P L)
        rw [normalFamily_decode_encode_bhist F, normalFamily_decode_encode_bhist X,
          normalFamily_decode_encode_bhist Y, normalFamily_decode_encode_bhist M,
          normalFamily_decode_encode_bhist E, normalFamily_decode_encode_bhist I,
          normalFamily_decode_encode_bhist Q, normalFamily_decode_encode_bhist H,
          normalFamily_decode_encode_bhist C, normalFamily_decode_encode_bhist P,
          normalFamily_decode_encode_bhist L]
  · rfl

end BEDC.Derived.NormalFamilyUp
