import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedDyadicRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedDyadicRealUp : Type where
  | mk (D S Q Lc R H C P N : BHist) : LocatedDyadicRealUp

def LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist h

def LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
        (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def LocatedDyadicRealTasteGate_single_carrier_alignment_fields :
    LocatedDyadicRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedDyadicRealUp.mk D S Q Lc R H C P N => [D, S, Q, Lc, R, H, C, P, N]

def LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow :
    LocatedDyadicRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (LocatedDyadicRealTasteGate_single_carrier_alignment_fields x).map
      LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist

def LocatedDyadicRealTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option LocatedDyadicRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [D, S, Q, Lc, R, H, C, P, N] =>
      some
        (LocatedDyadicRealUp.mk
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist D)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist S)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist Q)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist Lc)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist R)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist H)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist C)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist P)
          (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem LocatedDyadicRealTasteGate_single_carrier_alignment_round_trip
    (x : LocatedDyadicRealUp) :
    LocatedDyadicRealTasteGate_single_carrier_alignment_fromEventFlow
      (LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S Q Lc R H C P N =>
      change
        some
          (LocatedDyadicRealUp.mk
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist D))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist S))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist Q))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist Lc))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist R))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist H))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist C))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist P))
            (LocatedDyadicRealTasteGate_single_carrier_alignment_decodeBHist
              (LocatedDyadicRealTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (LocatedDyadicRealUp.mk D S Q Lc R H C P N)
      rw [LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode D,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode S,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode Lc,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode R,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode H,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode C,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode P,
        LocatedDyadicRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedDyadicRealUp} :
    LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow x =
        LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      LocatedDyadicRealTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow x) =
        LocatedDyadicRealTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg LocatedDyadicRealTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedDyadicRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedDyadicRealTasteGate_single_carrier_alignment_round_trip y)))

instance locatedDyadicRealBHistCarrier : BHistCarrier LocatedDyadicRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LocatedDyadicRealTasteGate_single_carrier_alignment_fromEventFlow

instance locatedDyadicRealChapterTasteGate : ChapterTasteGate LocatedDyadicRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      LocatedDyadicRealTasteGate_single_carrier_alignment_fromEventFlow
        (LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact LocatedDyadicRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedDyadicRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedDyadicRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedDyadicRealChapterTasteGate

theorem LocatedDyadicRealTasteGate_single_carrier_alignment :
    ChapterTasteGate LocatedDyadicRealUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact taste_gate

end BEDC.Derived.LocatedDyadicRealUp
