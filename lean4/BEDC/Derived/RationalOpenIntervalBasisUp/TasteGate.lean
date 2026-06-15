import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalOpenIntervalBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalOpenIntervalBasisUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (Q D M S G E H C P N : BHist) : RationalOpenIntervalBasisUp

def rationalOpenIntervalBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalOpenIntervalBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalOpenIntervalBasisEncodeBHist h

def rationalOpenIntervalBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalOpenIntervalBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalOpenIntervalBasisDecodeBHist tail)

private theorem RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fields :
    RationalOpenIntervalBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalOpenIntervalBasisUp.mk Q D M S G E H C P N => [Q, D, M, S, G, E, H, C, P, N]

def RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow :
    RationalOpenIntervalBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fields x).map
      rationalOpenIntervalBasisEncodeBHist

def RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RationalOpenIntervalBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [Q, D, M, S, G, E, H, C, P, N] =>
      some
        (RationalOpenIntervalBasisUp.mk
          (rationalOpenIntervalBasisDecodeBHist Q)
          (rationalOpenIntervalBasisDecodeBHist D)
          (rationalOpenIntervalBasisDecodeBHist M)
          (rationalOpenIntervalBasisDecodeBHist S)
          (rationalOpenIntervalBasisDecodeBHist G)
          (rationalOpenIntervalBasisDecodeBHist E)
          (rationalOpenIntervalBasisDecodeBHist H)
          (rationalOpenIntervalBasisDecodeBHist C)
          (rationalOpenIntervalBasisDecodeBHist P)
          (rationalOpenIntervalBasisDecodeBHist N))
  | _ => none

private theorem RationalOpenIntervalBasisTasteGate_single_carrier_alignment_round_trip
    (x : RationalOpenIntervalBasisUp) :
    RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fromEventFlow
      (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q D M S G E H C P N =>
      change
        some
          (RationalOpenIntervalBasisUp.mk
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist Q))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist D))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist M))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist S))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist G))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist E))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist H))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist C))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist P))
            (rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist N))) =
          some (RationalOpenIntervalBasisUp.mk Q D M S G E H C P N)
      rw [RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode Q,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode D,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode M,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode S,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode G,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode E,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode H,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode C,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode P,
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_decode_encode N]

private theorem RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalOpenIntervalBasisUp} :
    RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow x =
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fromEventFlow
          (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow x) =
        RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fromEventFlow
          (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_round_trip y)))

instance rationalOpenIntervalBasisBHistCarrier :
    BHistCarrier RationalOpenIntervalBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fromEventFlow

instance rationalOpenIntervalBasisChapterTasteGate :
    ChapterTasteGate RationalOpenIntervalBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fromEventFlow
        (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact RationalOpenIntervalBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RationalOpenIntervalBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RationalOpenIntervalBasisTasteGate_single_carrier_alignment :
    (∀ Q D M S G E H C P N : BHist,
      RationalOpenIntervalBasisTasteGate_single_carrier_alignment_fields
        (RationalOpenIntervalBasisUp.mk Q D M S G E H C P N) =
          [Q, D, M, S, G, E, H, C, P, N]) ∧
      (∀ h : BHist,
        rationalOpenIntervalBasisDecodeBHist (rationalOpenIntervalBasisEncodeBHist h) = h) ∧
          rationalOpenIntervalBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro Q D M S G E H C P N
    rfl
  · constructor
    · intro h
      induction h with
      | Empty => rfl
      | e0 h ih => exact congrArg BHist.e0 ih
      | e1 h ih => exact congrArg BHist.e1 ih
    · rfl

end BEDC.Derived.RationalOpenIntervalBasisUp
