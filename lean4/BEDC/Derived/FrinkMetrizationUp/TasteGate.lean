import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrinkMetrizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrinkMetrizationUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (U Q D P M T H C G N : BHist) : FrinkMetrizationUp

def FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist h

def FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
        (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FrinkMetrizationTasteGate_single_carrier_alignment_fields :
    FrinkMetrizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrinkMetrizationUp.mk U Q D P M T H C G N => [U, Q, D, P, M, T, H, C, G, N]

def FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow :
    FrinkMetrizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (FrinkMetrizationTasteGate_single_carrier_alignment_fields x).map
      FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist

def FrinkMetrizationTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option FrinkMetrizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [U, Q, D, P, M, T, H, C, G, N] =>
      some
        (FrinkMetrizationUp.mk
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist U)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist Q)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist D)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist P)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist M)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist T)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist H)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist C)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist G)
          (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem FrinkMetrizationTasteGate_single_carrier_alignment_round_trip
    (x : FrinkMetrizationUp) :
    FrinkMetrizationTasteGate_single_carrier_alignment_fromEventFlow
      (FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U Q D P M T H C G N =>
      change
        some
          (FrinkMetrizationUp.mk
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist U))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist Q))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist D))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist P))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist M))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist T))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist H))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist C))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist G))
            (FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
              (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (FrinkMetrizationUp.mk U Q D P M T H C G N)
      rw [FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode U,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode Q,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode D,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode P,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode M,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode T,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode H,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode C,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode G,
        FrinkMetrizationTasteGate_single_carrier_alignment_decode_encode N]

private theorem FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrinkMetrizationUp} :
    FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow x =
        FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FrinkMetrizationTasteGate_single_carrier_alignment_fromEventFlow
          (FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow x) =
        FrinkMetrizationTasteGate_single_carrier_alignment_fromEventFlow
          (FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FrinkMetrizationTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrinkMetrizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrinkMetrizationTasteGate_single_carrier_alignment_round_trip y)))

instance frinkMetrizationBHistCarrier : BHistCarrier FrinkMetrizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FrinkMetrizationTasteGate_single_carrier_alignment_fromEventFlow

instance frinkMetrizationChapterTasteGate : ChapterTasteGate FrinkMetrizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FrinkMetrizationTasteGate_single_carrier_alignment_fromEventFlow
        (FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact FrinkMetrizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrinkMetrizationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FrinkMetrizationTasteGate_single_carrier_alignment :
    (∀ U Q D P M T H C G N : BHist,
      FrinkMetrizationTasteGate_single_carrier_alignment_fields
        (FrinkMetrizationUp.mk U Q D P M T H C G N) =
          [U, Q, D, P, M, T, H, C, G, N]) ∧
      (∀ h : BHist,
        FrinkMetrizationTasteGate_single_carrier_alignment_decodeBHist
          (FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        FrinkMetrizationTasteGate_single_carrier_alignment_encodeBHist (BHist.e1 BHist.Empty) =
          [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro U Q D P M T H C G N
    rfl
  · constructor
    · intro h
      induction h with
      | Empty => rfl
      | e0 h ih => exact congrArg BHist.e0 ih
      | e1 h ih => exact congrArg BHist.e1 ih
    · rfl

end BEDC.Derived.FrinkMetrizationUp
