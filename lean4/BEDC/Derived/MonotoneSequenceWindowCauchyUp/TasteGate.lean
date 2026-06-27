import BEDC.Derived.MonotoneSequenceWindowCauchyUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneSequenceWindowCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

structure MonotoneSequenceWindowCauchyEventFlow where
  rows : List BHist

def monotoneSequenceWindowCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneSequenceWindowCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneSequenceWindowCauchyEncodeBHist h

def monotoneSequenceWindowCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneSequenceWindowCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneSequenceWindowCauchyDecodeBHist tail)

private theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      monotoneSequenceWindowCauchyDecodeBHist
        (monotoneSequenceWindowCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneSequenceWindowCauchyFields :
    MonotoneSequenceWindowCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneSequenceWindowCauchyUp.mk M B S R D E H C P N => [M, B, S, R, D, E, H, C, P, N]

def monotoneSequenceWindowCauchyToEventFlow
    (x : MonotoneSequenceWindowCauchyUp) :
    MonotoneSequenceWindowCauchyEventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  ⟨monotoneSequenceWindowCauchyFields x⟩

def monotoneSequenceWindowCauchyToGroundEventFlow :
    MonotoneSequenceWindowCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (monotoneSequenceWindowCauchyFields x).map
      monotoneSequenceWindowCauchyEncodeBHist

def monotoneSequenceWindowCauchyFromGroundEventFlow
    (ef : EventFlow) : Option MonotoneSequenceWindowCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | M :: B :: S :: R :: D :: E :: H :: C :: P :: N :: [] =>
      some
        (MonotoneSequenceWindowCauchyUp.mk
          (monotoneSequenceWindowCauchyDecodeBHist M)
          (monotoneSequenceWindowCauchyDecodeBHist B)
          (monotoneSequenceWindowCauchyDecodeBHist S)
          (monotoneSequenceWindowCauchyDecodeBHist R)
          (monotoneSequenceWindowCauchyDecodeBHist D)
          (monotoneSequenceWindowCauchyDecodeBHist E)
          (monotoneSequenceWindowCauchyDecodeBHist H)
          (monotoneSequenceWindowCauchyDecodeBHist C)
          (monotoneSequenceWindowCauchyDecodeBHist P)
          (monotoneSequenceWindowCauchyDecodeBHist N))
  | _ => none

private theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip
    (x : MonotoneSequenceWindowCauchyUp) :
    monotoneSequenceWindowCauchyFromGroundEventFlow
      (monotoneSequenceWindowCauchyToGroundEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M B S R D E H C P N =>
      change
        some
          (MonotoneSequenceWindowCauchyUp.mk
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist M))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist B))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist S))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist R))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist D))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist E))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist H))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist C))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist P))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist N))) =
          some (MonotoneSequenceWindowCauchyUp.mk M B S R D E H C P N)
      rw [MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode M,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode B,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode S,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode R,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode D,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode E,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode H,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode C,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode P,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode N]

private theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MonotoneSequenceWindowCauchyUp} :
    monotoneSequenceWindowCauchyToGroundEventFlow x =
        monotoneSequenceWindowCauchyToGroundEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneSequenceWindowCauchyFromGroundEventFlow
          (monotoneSequenceWindowCauchyToGroundEventFlow x) =
        monotoneSequenceWindowCauchyFromGroundEventFlow
          (monotoneSequenceWindowCauchyToGroundEventFlow y) :=
    congrArg monotoneSequenceWindowCauchyFromGroundEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip y)))

instance monotoneSequenceWindowCauchyBHistCarrier :
    BHistCarrier MonotoneSequenceWindowCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneSequenceWindowCauchyToGroundEventFlow
  fromEventFlow := monotoneSequenceWindowCauchyFromGroundEventFlow

instance monotoneSequenceWindowCauchyChapterTasteGate :
    ChapterTasteGate MonotoneSequenceWindowCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneSequenceWindowCauchyFromGroundEventFlow
        (monotoneSequenceWindowCauchyToGroundEventFlow x) = some x
    exact MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MonotoneSequenceWindowCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneSequenceWindowCauchyChapterTasteGate

theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEncodeBHist h) =
        h) ∧
      (∀ x : MonotoneSequenceWindowCauchyUp,
        (monotoneSequenceWindowCauchyToEventFlow x).rows =
          monotoneSequenceWindowCauchyFields x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode,
      fun x => rfl⟩

end BEDC.Derived.MonotoneSequenceWindowCauchyUp
