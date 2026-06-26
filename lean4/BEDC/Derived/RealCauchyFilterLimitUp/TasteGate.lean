import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyFilterLimitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyFilterLimitUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (F B W R D E H C P N : BHist) : RealCauchyFilterLimitUp

def RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist h

def RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
        (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RealCauchyFilterLimitTasteGate_single_carrier_alignment_fields :
    RealCauchyFilterLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyFilterLimitUp.mk F B W R D E H C P N => [F, B, W, R, D, E, H, C, P, N]

def RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow :
    RealCauchyFilterLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RealCauchyFilterLimitTasteGate_single_carrier_alignment_fields x).map
      RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist

def RealCauchyFilterLimitTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RealCauchyFilterLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [F, B, W, R, D, E, H, C, P, N] =>
      some
        (RealCauchyFilterLimitUp.mk
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist F)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist B)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist W)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist R)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist D)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist E)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist H)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist C)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist P)
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem RealCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip
    (x : RealCauchyFilterLimitUp) :
    RealCauchyFilterLimitTasteGate_single_carrier_alignment_fromEventFlow
        (RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F B W R D E H C P N =>
      change
        some
          (RealCauchyFilterLimitUp.mk
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist F))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist B))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist W))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist R))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist D))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist E))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist H))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist C))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist P))
            (RealCauchyFilterLimitTasteGate_single_carrier_alignment_decodeBHist
              (RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RealCauchyFilterLimitUp.mk F B W R D E H C P N)
      rw [RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode F,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode B,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode W,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode R,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode D,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode E,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode H,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode C,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode P,
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealCauchyFilterLimitUp} :
    RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow x =
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RealCauchyFilterLimitTasteGate_single_carrier_alignment_fromEventFlow
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        RealCauchyFilterLimitTasteGate_single_carrier_alignment_fromEventFlow
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RealCauchyFilterLimitTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip y)))

instance realCauchyFilterLimitBHistCarrier : BHistCarrier RealCauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RealCauchyFilterLimitTasteGate_single_carrier_alignment_fromEventFlow

instance realCauchyFilterLimitChapterTasteGate :
    ChapterTasteGate RealCauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RealCauchyFilterLimitTasteGate_single_carrier_alignment_fromEventFlow
          (RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RealCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealCauchyFilterLimitTasteGate_single_carrier_alignment :
    (∀ F B W R D E H C P N : BHist,
      RealCauchyFilterLimitTasteGate_single_carrier_alignment_fields
        (RealCauchyFilterLimitUp.mk F B W R D E H C P N) =
          [F, B, W, R, D, E, H, C, P, N]) ∧
      RealCauchyFilterLimitTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) =
        [BMark.b1] ∧
        ∃ replay : BHist, Cont replay replay replay := by
  -- BEDC touchpoint anchor: BHist BMark Cont ChapterTasteGate
  constructor
  · intro F B W R D E H C P N
    rfl
  · constructor
    · rfl
    · exact ⟨BHist.Empty, rfl⟩

end BEDC.Derived.RealCauchyFilterLimitUp
