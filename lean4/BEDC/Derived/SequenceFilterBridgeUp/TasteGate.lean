import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequenceFilterBridgeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequenceFilterBridgeUp : Type where
  | mk (S F Q T R E H C P N : BHist) : SequenceFilterBridgeUp
  deriving DecidableEq

def SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist h

def SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
        (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fields :
    SequenceFilterBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequenceFilterBridgeUp.mk S F Q T R E H C P N => [S, F, Q, T, R, E, H, C, P, N]

def SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow :
    SequenceFilterBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fields x).map
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist

def SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option SequenceFilterBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: F :: Q :: T :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (SequenceFilterBridgeUp.mk
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist S)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist F)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist Q)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist T)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist R)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist E)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist H)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist C)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist P)
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem SequenceFilterBridgeUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SequenceFilterBridgeUp,
      SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fromEventFlow
        (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F Q T R E H C P N =>
      change
        some
          (SequenceFilterBridgeUp.mk
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist S))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist F))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist Q))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist T))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist R))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist E))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist H))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist C))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist P))
            (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decodeBHist
              (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (SequenceFilterBridgeUp.mk S F Q T R E H C P N)
      rw [SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode S,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode F,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode Q,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode T,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode R,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode E,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode H,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode C,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode P,
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequenceFilterBridgeUp} :
    SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow x =
      SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fromEventFlow
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow x) =
        SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fromEventFlow
          (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_round_trip y)))

instance SequenceFilterBridgeUpTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier SequenceFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fromEventFlow

instance SequenceFilterBridgeUpTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate SequenceFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      SequenceFilterBridgeUpTasteGate_single_carrier_alignment_fromEventFlow
        (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact SequenceFilterBridgeUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SequenceFilterBridgeUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SequenceFilterBridgeUpTasteGate_single_carrier_alignment
    (G : SequenceFilterBridgeUp) :
    ∃ S F Q T R E H C P N : BHist,
      G = SequenceFilterBridgeUp.mk S F Q T R E H C P N ∧
        Cont S BHist.Empty S ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases G with
  | mk S F Q T R E H C P N =>
      exact
        ⟨S, F, Q, T, R, E, H, C, P, N, rfl, cont_right_unit S,
          hsame_refl N⟩

end BEDC.Derived.SequenceFilterBridgeUp
