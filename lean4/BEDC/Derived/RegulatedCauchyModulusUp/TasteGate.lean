import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedCauchyModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedCauchyModulusUp : Type where
  | mk (R Q W D E H C P N : BHist) : RegulatedCauchyModulusUp
  deriving DecidableEq

def regulatedCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedCauchyModulusEncodeBHist h

def regulatedCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedCauchyModulusDecodeBHist tail)

private theorem regulatedCauchyModulus_decode_encode_bhist :
    ∀ h : BHist,
      regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedCauchyModulusToEventFlow : RegulatedCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedCauchyModulusUp.mk R Q W D E H C P N =>
      [regulatedCauchyModulusEncodeBHist R,
        regulatedCauchyModulusEncodeBHist Q,
        regulatedCauchyModulusEncodeBHist W,
        regulatedCauchyModulusEncodeBHist D,
        regulatedCauchyModulusEncodeBHist E,
        regulatedCauchyModulusEncodeBHist H,
        regulatedCauchyModulusEncodeBHist C,
        regulatedCauchyModulusEncodeBHist P,
        regulatedCauchyModulusEncodeBHist N]

private def regulatedCauchyModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regulatedCauchyModulusEventAt index rest

def regulatedCauchyModulusFromEventFlow :
    EventFlow → Option RegulatedCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegulatedCauchyModulusUp.mk
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 0 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 1 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 2 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 3 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 4 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 5 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 6 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 7 ef))
        (regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEventAt 8 ef)))

private theorem regulatedCauchyModulus_round_trip :
    ∀ x : RegulatedCauchyModulusUp,
      regulatedCauchyModulusFromEventFlow
          (regulatedCauchyModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q W D E H C P N =>
      change
        some
            (RegulatedCauchyModulusUp.mk
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist R))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist Q))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist W))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist D))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist E))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist H))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist C))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist P))
              (regulatedCauchyModulusDecodeBHist
                (regulatedCauchyModulusEncodeBHist N))) =
          some (RegulatedCauchyModulusUp.mk R Q W D E H C P N)
      rw [regulatedCauchyModulus_decode_encode_bhist R,
        regulatedCauchyModulus_decode_encode_bhist Q,
        regulatedCauchyModulus_decode_encode_bhist W,
        regulatedCauchyModulus_decode_encode_bhist D,
        regulatedCauchyModulus_decode_encode_bhist E,
        regulatedCauchyModulus_decode_encode_bhist H,
        regulatedCauchyModulus_decode_encode_bhist C,
        regulatedCauchyModulus_decode_encode_bhist P,
        regulatedCauchyModulus_decode_encode_bhist N]

private theorem regulatedCauchyModulusToEventFlow_injective
    {x y : RegulatedCauchyModulusUp} :
    regulatedCauchyModulusToEventFlow x =
      regulatedCauchyModulusToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedCauchyModulusFromEventFlow
          (regulatedCauchyModulusToEventFlow x) =
        regulatedCauchyModulusFromEventFlow
          (regulatedCauchyModulusToEventFlow y) :=
    congrArg regulatedCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regulatedCauchyModulus_round_trip x).symm
      (Eq.trans hread (regulatedCauchyModulus_round_trip y)))

instance regulatedCauchyModulusBHistCarrier :
    BHistCarrier RegulatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedCauchyModulusToEventFlow
  fromEventFlow := regulatedCauchyModulusFromEventFlow

instance regulatedCauchyModulusChapterTasteGate :
    ChapterTasteGate RegulatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regulatedCauchyModulusFromEventFlow
          (regulatedCauchyModulusToEventFlow x) =
        some x
    exact regulatedCauchyModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regulatedCauchyModulusToEventFlow_injective heq)

theorem RegulatedCauchyModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regulatedCauchyModulusDecodeBHist (regulatedCauchyModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegulatedCauchyModulusUp) ∧
        Nonempty (ChapterTasteGate RegulatedCauchyModulusUp) ∧
          regulatedCauchyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regulatedCauchyModulus_decode_encode_bhist,
      ⟨regulatedCauchyModulusBHistCarrier⟩,
      ⟨regulatedCauchyModulusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegulatedCauchyModulusUp.TasteGate
