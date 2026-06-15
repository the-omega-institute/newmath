import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzRealMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzRealMapUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (S T K W R M H C P N : BHist) : LipschitzRealMapUp

def lipschitzRealMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzRealMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzRealMapEncodeBHist h

def lipschitzRealMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzRealMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzRealMapDecodeBHist tail)

private theorem LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def LipschitzRealMapTasteGate_single_carrier_alignment_fields :
    LipschitzRealMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzRealMapUp.mk S T K W R M H C P N => [S, T, K, W, R, M, H, C, P, N]

def LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow :
    LipschitzRealMapUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (LipschitzRealMapTasteGate_single_carrier_alignment_fields x).map
      lipschitzRealMapEncodeBHist

def LipschitzRealMapTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option LipschitzRealMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, T, K, W, R, M, H, C, P, N] =>
      some
        (LipschitzRealMapUp.mk
          (lipschitzRealMapDecodeBHist S)
          (lipschitzRealMapDecodeBHist T)
          (lipschitzRealMapDecodeBHist K)
          (lipschitzRealMapDecodeBHist W)
          (lipschitzRealMapDecodeBHist R)
          (lipschitzRealMapDecodeBHist M)
          (lipschitzRealMapDecodeBHist H)
          (lipschitzRealMapDecodeBHist C)
          (lipschitzRealMapDecodeBHist P)
          (lipschitzRealMapDecodeBHist N))
  | _ => none

private theorem LipschitzRealMapTasteGate_single_carrier_alignment_round_trip
    (x : LipschitzRealMapUp) :
    LipschitzRealMapTasteGate_single_carrier_alignment_fromEventFlow
      (LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T K W R M H C P N =>
      change
        some
          (LipschitzRealMapUp.mk
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist S))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist T))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist K))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist W))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist R))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist M))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist H))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist C))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist P))
            (lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist N))) =
          some (LipschitzRealMapUp.mk S T K W R M H C P N)
      rw [LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode S,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode T,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode K,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode W,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode R,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode M,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode H,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode C,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode P,
        LipschitzRealMapTasteGate_single_carrier_alignment_decode_encode N]

private theorem LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LipschitzRealMapUp} :
    LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow x =
        LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      LipschitzRealMapTasteGate_single_carrier_alignment_fromEventFlow
          (LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow x) =
        LipschitzRealMapTasteGate_single_carrier_alignment_fromEventFlow
          (LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg LipschitzRealMapTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LipschitzRealMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LipschitzRealMapTasteGate_single_carrier_alignment_round_trip y)))

instance lipschitzRealMapBHistCarrier : BHistCarrier LipschitzRealMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LipschitzRealMapTasteGate_single_carrier_alignment_fromEventFlow

instance lipschitzRealMapChapterTasteGate : ChapterTasteGate LipschitzRealMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      LipschitzRealMapTasteGate_single_carrier_alignment_fromEventFlow
        (LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact LipschitzRealMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LipschitzRealMapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LipschitzRealMapTasteGate_single_carrier_alignment :
    (∀ S T K W R M H C P N : BHist,
      LipschitzRealMapTasteGate_single_carrier_alignment_fields
        (LipschitzRealMapUp.mk S T K W R M H C P N) =
          [S, T, K, W, R, M, H, C, P, N]) ∧
      (∀ h : BHist, lipschitzRealMapDecodeBHist (lipschitzRealMapEncodeBHist h) = h) ∧
          lipschitzRealMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro S T K W R M H C P N
    rfl
  · constructor
    · intro h
      induction h with
      | Empty => rfl
      | e0 h ih => exact congrArg BHist.e0 ih
      | e1 h ih => exact congrArg BHist.e1 ih
    · rfl

end BEDC.Derived.LipschitzRealMapUp
