import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UrysohnMetrizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UrysohnMetrizationUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (T N S Hd B F D M G R Q C P L : BHist) : UrysohnMetrizationUp

def urysohnMetrizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: urysohnMetrizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: urysohnMetrizationEncodeBHist h

def urysohnMetrizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (urysohnMetrizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (urysohnMetrizationDecodeBHist tail)

private theorem UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def UrysohnMetrizationTasteGate_single_carrier_alignment_fields :
    UrysohnMetrizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UrysohnMetrizationUp.mk T N S Hd B F D M G R Q C P L =>
      [T, N, S, Hd, B, F, D, M, G, R, Q, C, P, L]

def UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow :
    UrysohnMetrizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (UrysohnMetrizationTasteGate_single_carrier_alignment_fields x).map
      urysohnMetrizationEncodeBHist

def UrysohnMetrizationTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option UrysohnMetrizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [T, N, S, Hd, B, F, D, M, G, R, Q, C, P, L] =>
      some
        (UrysohnMetrizationUp.mk
          (urysohnMetrizationDecodeBHist T)
          (urysohnMetrizationDecodeBHist N)
          (urysohnMetrizationDecodeBHist S)
          (urysohnMetrizationDecodeBHist Hd)
          (urysohnMetrizationDecodeBHist B)
          (urysohnMetrizationDecodeBHist F)
          (urysohnMetrizationDecodeBHist D)
          (urysohnMetrizationDecodeBHist M)
          (urysohnMetrizationDecodeBHist G)
          (urysohnMetrizationDecodeBHist R)
          (urysohnMetrizationDecodeBHist Q)
          (urysohnMetrizationDecodeBHist C)
          (urysohnMetrizationDecodeBHist P)
          (urysohnMetrizationDecodeBHist L))
  | _ => none

private theorem UrysohnMetrizationTasteGate_single_carrier_alignment_round_trip
    (x : UrysohnMetrizationUp) :
    UrysohnMetrizationTasteGate_single_carrier_alignment_fromEventFlow
      (UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T N S Hd B F D M G R Q C P L =>
      change
        some
          (UrysohnMetrizationUp.mk
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist T))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist N))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist S))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist Hd))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist B))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist F))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist D))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist M))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist G))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist R))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist Q))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist C))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist P))
            (urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist L))) =
          some (UrysohnMetrizationUp.mk T N S Hd B F D M G R Q C P L)
      rw [UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode T,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode N,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode S,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode Hd,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode B,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode F,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode D,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode M,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode G,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode R,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode Q,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode C,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode P,
        UrysohnMetrizationTasteGate_single_carrier_alignment_decode_encode L]

private theorem UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UrysohnMetrizationUp} :
    UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow x =
        UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      UrysohnMetrizationTasteGate_single_carrier_alignment_fromEventFlow
          (UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow x) =
        UrysohnMetrizationTasteGate_single_carrier_alignment_fromEventFlow
          (UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg UrysohnMetrizationTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UrysohnMetrizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UrysohnMetrizationTasteGate_single_carrier_alignment_round_trip y)))

instance urysohnMetrizationBHistCarrier : BHistCarrier UrysohnMetrizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := UrysohnMetrizationTasteGate_single_carrier_alignment_fromEventFlow

instance urysohnMetrizationChapterTasteGate :
    ChapterTasteGate UrysohnMetrizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      UrysohnMetrizationTasteGate_single_carrier_alignment_fromEventFlow
        (UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact UrysohnMetrizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UrysohnMetrizationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UrysohnMetrizationTasteGate_single_carrier_alignment :
    (∀ T N S Hd B F D M G R Q C P L : BHist,
      UrysohnMetrizationTasteGate_single_carrier_alignment_fields
        (UrysohnMetrizationUp.mk T N S Hd B F D M G R Q C P L) =
          [T, N, S, Hd, B, F, D, M, G, R, Q, C, P, L]) ∧
      (∀ h : BHist, urysohnMetrizationDecodeBHist (urysohnMetrizationEncodeBHist h) = h) ∧
          urysohnMetrizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro T N S Hd B F D M G R Q C P L
    rfl
  · constructor
    · intro h
      induction h with
      | Empty => rfl
      | e0 h ih => exact congrArg BHist.e0 ih
      | e1 h ih => exact congrArg BHist.e1 ih
    · rfl

end BEDC.Derived.UrysohnMetrizationUp
