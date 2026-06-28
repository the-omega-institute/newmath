import BEDC.Derived.DyadicToleranceCompositionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicToleranceCompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

structure DyadicToleranceCompositionEventFlow where
  rows : List BHist

def dyadicToleranceCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicToleranceCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicToleranceCompositionEncodeBHist h

def dyadicToleranceCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicToleranceCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicToleranceCompositionDecodeBHist tail)

private theorem DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicToleranceCompositionDecodeBHist
        (dyadicToleranceCompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicToleranceCompositionFields :
    DyadicToleranceCompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicToleranceCompositionUp.mk Q S0 S1 B0 B1 Qp W0 W1 R0 R1 D E H C P N =>
      [Q, S0, S1, B0, B1, Qp, W0, W1, R0, R1, D, E, H, C, P, N]

def dyadicToleranceCompositionToEventFlow
    (x : DyadicToleranceCompositionUp) :
    DyadicToleranceCompositionEventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  ⟨dyadicToleranceCompositionFields x⟩

def dyadicToleranceCompositionToGroundEventFlow :
    DyadicToleranceCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicToleranceCompositionFields x).map dyadicToleranceCompositionEncodeBHist

def dyadicToleranceCompositionFromGroundEventFlow
    (ef : EventFlow) : Option DyadicToleranceCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | Q :: S0 :: S1 :: B0 :: B1 :: Qp :: W0 :: W1 :: R0 :: R1 :: D :: E :: H :: C :: P :: N :: [] =>
      some
        (DyadicToleranceCompositionUp.mk
          (dyadicToleranceCompositionDecodeBHist Q)
          (dyadicToleranceCompositionDecodeBHist S0)
          (dyadicToleranceCompositionDecodeBHist S1)
          (dyadicToleranceCompositionDecodeBHist B0)
          (dyadicToleranceCompositionDecodeBHist B1)
          (dyadicToleranceCompositionDecodeBHist Qp)
          (dyadicToleranceCompositionDecodeBHist W0)
          (dyadicToleranceCompositionDecodeBHist W1)
          (dyadicToleranceCompositionDecodeBHist R0)
          (dyadicToleranceCompositionDecodeBHist R1)
          (dyadicToleranceCompositionDecodeBHist D)
          (dyadicToleranceCompositionDecodeBHist E)
          (dyadicToleranceCompositionDecodeBHist H)
          (dyadicToleranceCompositionDecodeBHist C)
          (dyadicToleranceCompositionDecodeBHist P)
          (dyadicToleranceCompositionDecodeBHist N))
  | _ => none

private theorem DyadicToleranceCompositionTasteGate_single_carrier_alignment_round_trip
    (x : DyadicToleranceCompositionUp) :
    dyadicToleranceCompositionFromGroundEventFlow
      (dyadicToleranceCompositionToGroundEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q S0 S1 B0 B1 Qp W0 W1 R0 R1 D E H C P N =>
      change
        some
          (DyadicToleranceCompositionUp.mk
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist Q))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist S0))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist S1))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist B0))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist B1))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist Qp))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist W0))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist W1))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist R0))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist R1))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist D))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist E))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist H))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist C))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist P))
            (dyadicToleranceCompositionDecodeBHist
              (dyadicToleranceCompositionEncodeBHist N))) =
          some
            (DyadicToleranceCompositionUp.mk Q S0 S1 B0 B1 Qp W0 W1 R0 R1 D E H C P N)
      rw [DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode S0,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode S1,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode B0,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode B1,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode Qp,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode W0,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode W1,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode R0,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode R1,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode D,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode E,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode H,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode C,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode P,
        DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicToleranceCompositionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicToleranceCompositionUp} :
    dyadicToleranceCompositionToGroundEventFlow x =
        dyadicToleranceCompositionToGroundEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicToleranceCompositionFromGroundEventFlow
          (dyadicToleranceCompositionToGroundEventFlow x) =
        dyadicToleranceCompositionFromGroundEventFlow
          (dyadicToleranceCompositionToGroundEventFlow y) :=
    congrArg dyadicToleranceCompositionFromGroundEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicToleranceCompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicToleranceCompositionTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicToleranceCompositionBHistCarrier :
    BHistCarrier DyadicToleranceCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicToleranceCompositionToGroundEventFlow
  fromEventFlow := dyadicToleranceCompositionFromGroundEventFlow

instance dyadicToleranceCompositionChapterTasteGate :
    ChapterTasteGate DyadicToleranceCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicToleranceCompositionFromGroundEventFlow
        (dyadicToleranceCompositionToGroundEventFlow x) = some x
    exact DyadicToleranceCompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicToleranceCompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicToleranceCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicToleranceCompositionChapterTasteGate

theorem DyadicToleranceCompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicToleranceCompositionDecodeBHist
          (dyadicToleranceCompositionEncodeBHist h) =
        h) ∧
      (∀ x : DyadicToleranceCompositionUp,
        (dyadicToleranceCompositionToEventFlow x).rows =
          dyadicToleranceCompositionFields x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicToleranceCompositionTasteGate_single_carrier_alignment_decode_encode,
      fun x => rfl⟩

end BEDC.Derived.DyadicToleranceCompositionUp
