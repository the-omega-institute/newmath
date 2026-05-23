import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularCauchyLimitSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularCauchyLimitSealUp : Type where
  | mk (D S R M E U V H C P N : BHist) : BishopRegularCauchyLimitSealUp
  deriving DecidableEq

def bishopRegularCauchyLimitSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularCauchyLimitSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularCauchyLimitSealEncodeBHist h

def bishopRegularCauchyLimitSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularCauchyLimitSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularCauchyLimitSealDecodeBHist tail)

private theorem BishopRegularCauchyLimitSealTasteGate_decode_encode :
    ∀ h : BHist,
      bishopRegularCauchyLimitSealDecodeBHist
        (bishopRegularCauchyLimitSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRegularCauchyLimitSealToEventFlow :
    BishopRegularCauchyLimitSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularCauchyLimitSealUp.mk D S R M E U V H C P N =>
      [bishopRegularCauchyLimitSealEncodeBHist D,
        bishopRegularCauchyLimitSealEncodeBHist S,
        bishopRegularCauchyLimitSealEncodeBHist R,
        bishopRegularCauchyLimitSealEncodeBHist M,
        bishopRegularCauchyLimitSealEncodeBHist E,
        bishopRegularCauchyLimitSealEncodeBHist U,
        bishopRegularCauchyLimitSealEncodeBHist V,
        bishopRegularCauchyLimitSealEncodeBHist H,
        bishopRegularCauchyLimitSealEncodeBHist C,
        bishopRegularCauchyLimitSealEncodeBHist P,
        bishopRegularCauchyLimitSealEncodeBHist N]

private def bishopRegularCauchyLimitSealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopRegularCauchyLimitSealEventAtDefault index rest

def bishopRegularCauchyLimitSealFromEventFlow :
    EventFlow → Option BishopRegularCauchyLimitSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopRegularCauchyLimitSealUp.mk
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 0 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 1 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 2 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 3 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 4 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 5 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 6 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 7 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 8 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 9 ef))
          (bishopRegularCauchyLimitSealDecodeBHist
            (bishopRegularCauchyLimitSealEventAtDefault 10 ef)))

private theorem BishopRegularCauchyLimitSealTasteGate_round_trip
    (x : BishopRegularCauchyLimitSealUp) :
    bishopRegularCauchyLimitSealFromEventFlow
      (bishopRegularCauchyLimitSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R M E U V H C P N =>
      change
        some
          (BishopRegularCauchyLimitSealUp.mk
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist D))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist S))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist R))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist M))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist E))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist U))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist V))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist H))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist C))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist P))
            (bishopRegularCauchyLimitSealDecodeBHist
              (bishopRegularCauchyLimitSealEncodeBHist N))) =
          some (BishopRegularCauchyLimitSealUp.mk D S R M E U V H C P N)
      rw [BishopRegularCauchyLimitSealTasteGate_decode_encode D,
        BishopRegularCauchyLimitSealTasteGate_decode_encode S,
        BishopRegularCauchyLimitSealTasteGate_decode_encode R,
        BishopRegularCauchyLimitSealTasteGate_decode_encode M,
        BishopRegularCauchyLimitSealTasteGate_decode_encode E,
        BishopRegularCauchyLimitSealTasteGate_decode_encode U,
        BishopRegularCauchyLimitSealTasteGate_decode_encode V,
        BishopRegularCauchyLimitSealTasteGate_decode_encode H,
        BishopRegularCauchyLimitSealTasteGate_decode_encode C,
        BishopRegularCauchyLimitSealTasteGate_decode_encode P,
        BishopRegularCauchyLimitSealTasteGate_decode_encode N]

private theorem BishopRegularCauchyLimitSealTasteGate_toEventFlow_injective
    {x y : BishopRegularCauchyLimitSealUp} :
    bishopRegularCauchyLimitSealToEventFlow x =
      bishopRegularCauchyLimitSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularCauchyLimitSealFromEventFlow
          (bishopRegularCauchyLimitSealToEventFlow x) =
        bishopRegularCauchyLimitSealFromEventFlow
          (bishopRegularCauchyLimitSealToEventFlow y) :=
    congrArg bishopRegularCauchyLimitSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopRegularCauchyLimitSealTasteGate_round_trip x).symm
      (Eq.trans hread (BishopRegularCauchyLimitSealTasteGate_round_trip y)))

instance bishopRegularCauchyLimitSealBHistCarrier :
    BHistCarrier BishopRegularCauchyLimitSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularCauchyLimitSealToEventFlow
  fromEventFlow := bishopRegularCauchyLimitSealFromEventFlow

instance bishopRegularCauchyLimitSealChapterTasteGate :
    ChapterTasteGate BishopRegularCauchyLimitSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRegularCauchyLimitSealFromEventFlow
        (bishopRegularCauchyLimitSealToEventFlow x) = some x
    exact BishopRegularCauchyLimitSealTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopRegularCauchyLimitSealTasteGate_toEventFlow_injective heq)

theorem BishopRegularCauchyLimitSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRegularCauchyLimitSealDecodeBHist
        (bishopRegularCauchyLimitSealEncodeBHist h) = h) ∧
      (∀ x : BishopRegularCauchyLimitSealUp,
        bishopRegularCauchyLimitSealFromEventFlow
          (bishopRegularCauchyLimitSealToEventFlow x) = some x) ∧
        (∀ x y : BishopRegularCauchyLimitSealUp,
          bishopRegularCauchyLimitSealToEventFlow x =
            bishopRegularCauchyLimitSealToEventFlow y → x = y) ∧
          bishopRegularCauchyLimitSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRegularCauchyLimitSealTasteGate_decode_encode,
      BishopRegularCauchyLimitSealTasteGate_round_trip,
      (fun _ _ heq => BishopRegularCauchyLimitSealTasteGate_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopRegularCauchyLimitSealUp
