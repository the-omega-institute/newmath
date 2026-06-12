import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLimitUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLimitUniquenessUp : Type where
  | mk (L R D W Q E H C P N : BHist) : RegularCauchyLimitUniquenessUp
  deriving DecidableEq

def regularCauchyLimitUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLimitUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLimitUniquenessEncodeBHist h

def regularCauchyLimitUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLimitUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLimitUniquenessDecodeBHist tail)

private theorem regularCauchyLimitUniqueness_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLimitUniquenessToEventFlow :
    RegularCauchyLimitUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLimitUniquenessUp.mk L R D W Q E H C P N =>
      [regularCauchyLimitUniquenessEncodeBHist L,
        regularCauchyLimitUniquenessEncodeBHist R,
        regularCauchyLimitUniquenessEncodeBHist D,
        regularCauchyLimitUniquenessEncodeBHist W,
        regularCauchyLimitUniquenessEncodeBHist Q,
        regularCauchyLimitUniquenessEncodeBHist E,
        regularCauchyLimitUniquenessEncodeBHist H,
        regularCauchyLimitUniquenessEncodeBHist C,
        regularCauchyLimitUniquenessEncodeBHist P,
        regularCauchyLimitUniquenessEncodeBHist N]

private def regularCauchyLimitUniquenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLimitUniquenessEventAtDefault index rest

def regularCauchyLimitUniquenessFromEventFlow
    (ef : EventFlow) : Option RegularCauchyLimitUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLimitUniquenessUp.mk
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 0 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 1 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 2 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 3 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 4 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 5 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 6 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 7 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 8 ef))
      (regularCauchyLimitUniquenessDecodeBHist
        (regularCauchyLimitUniquenessEventAtDefault 9 ef)))

private theorem regularCauchyLimitUniqueness_round_trip :
    ∀ x : RegularCauchyLimitUniquenessUp,
      regularCauchyLimitUniquenessFromEventFlow
        (regularCauchyLimitUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R D W Q E H C P N =>
      change
        some
            (RegularCauchyLimitUniquenessUp.mk
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist L))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist R))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist D))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist W))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist Q))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist E))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist H))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist C))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist P))
              (regularCauchyLimitUniquenessDecodeBHist
                (regularCauchyLimitUniquenessEncodeBHist N))) =
          some (RegularCauchyLimitUniquenessUp.mk L R D W Q E H C P N)
      rw [regularCauchyLimitUniqueness_decode_encode_bhist L,
        regularCauchyLimitUniqueness_decode_encode_bhist R,
        regularCauchyLimitUniqueness_decode_encode_bhist D,
        regularCauchyLimitUniqueness_decode_encode_bhist W,
        regularCauchyLimitUniqueness_decode_encode_bhist Q,
        regularCauchyLimitUniqueness_decode_encode_bhist E,
        regularCauchyLimitUniqueness_decode_encode_bhist H,
        regularCauchyLimitUniqueness_decode_encode_bhist C,
        regularCauchyLimitUniqueness_decode_encode_bhist P,
        regularCauchyLimitUniqueness_decode_encode_bhist N]

private theorem regularCauchyLimitUniquenessToEventFlow_injective
    {x y : RegularCauchyLimitUniquenessUp} :
    regularCauchyLimitUniquenessToEventFlow x =
      regularCauchyLimitUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLimitUniquenessFromEventFlow
          (regularCauchyLimitUniquenessToEventFlow x) =
        regularCauchyLimitUniquenessFromEventFlow
          (regularCauchyLimitUniquenessToEventFlow y) :=
    congrArg regularCauchyLimitUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLimitUniqueness_round_trip x).symm
      (Eq.trans hread (regularCauchyLimitUniqueness_round_trip y)))

instance regularCauchyLimitUniquenessBHistCarrier :
    BHistCarrier RegularCauchyLimitUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLimitUniquenessToEventFlow
  fromEventFlow := regularCauchyLimitUniquenessFromEventFlow

instance regularCauchyLimitUniquenessChapterTasteGate :
    ChapterTasteGate RegularCauchyLimitUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLimitUniquenessFromEventFlow
        (regularCauchyLimitUniquenessToEventFlow x) = some x
    exact regularCauchyLimitUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLimitUniquenessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyLimitUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLimitUniquenessChapterTasteGate

theorem RegularCauchyLimitUniquenessTasteGate_single_carrier_alignment :
    regularCauchyLimitUniquenessEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist,
        regularCauchyLimitUniquenessDecodeBHist
          (regularCauchyLimitUniquenessEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLimitUniquenessUp,
        regularCauchyLimitUniquenessFromEventFlow
          (regularCauchyLimitUniquenessToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyLimitUniquenessUp,
        regularCauchyLimitUniquenessToEventFlow x =
          regularCauchyLimitUniquenessToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      regularCauchyLimitUniqueness_decode_encode_bhist,
      regularCauchyLimitUniqueness_round_trip,
      fun _ _ heq => regularCauchyLimitUniquenessToEventFlow_injective heq⟩

end BEDC.Derived.RegularCauchyLimitUniquenessUp
