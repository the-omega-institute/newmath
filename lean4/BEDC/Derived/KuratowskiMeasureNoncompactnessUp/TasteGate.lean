import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiMeasureNoncompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiMeasureNoncompactnessUp : Type where
  | packet (X C T E D V H R P N : BHist) : KuratowskiMeasureNoncompactnessUp
  deriving DecidableEq

def kuratowskiMeasureNoncompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiMeasureNoncompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiMeasureNoncompactnessEncodeBHist h

def kuratowskiMeasureNoncompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiMeasureNoncompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiMeasureNoncompactnessDecodeBHist tail)

private theorem KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiMeasureNoncompactnessFields :
    KuratowskiMeasureNoncompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiMeasureNoncompactnessUp.packet X C T E D V H R P N =>
      [X, C, T, E, D, V, H, R, P, N]

def kuratowskiMeasureNoncompactnessToEventFlow :
    KuratowskiMeasureNoncompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kuratowskiMeasureNoncompactnessFields x).map
      kuratowskiMeasureNoncompactnessEncodeBHist

private def kuratowskiMeasureNoncompactnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kuratowskiMeasureNoncompactnessEventAt index rest

def kuratowskiMeasureNoncompactnessFromEventFlow
    (ef : EventFlow) : Option KuratowskiMeasureNoncompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KuratowskiMeasureNoncompactnessUp.packet
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 0 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 1 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 2 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 3 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 4 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 5 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 6 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 7 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 8 ef))
      (kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEventAt 9 ef)))

private theorem KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_round_trip
    (x : KuratowskiMeasureNoncompactnessUp) :
    kuratowskiMeasureNoncompactnessFromEventFlow
      (kuratowskiMeasureNoncompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet X C T E D V H R P N =>
      change
        some
          (KuratowskiMeasureNoncompactnessUp.packet
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist X))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist C))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist T))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist E))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist D))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist V))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist H))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist R))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist P))
            (kuratowskiMeasureNoncompactnessDecodeBHist
              (kuratowskiMeasureNoncompactnessEncodeBHist N))) =
          some (KuratowskiMeasureNoncompactnessUp.packet X C T E D V H R P N)
      rw [KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode X,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode C,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode T,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode E,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode D,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode V,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode H,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode R,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode P,
        KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KuratowskiMeasureNoncompactnessUp} :
    kuratowskiMeasureNoncompactnessToEventFlow x =
      kuratowskiMeasureNoncompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiMeasureNoncompactnessFromEventFlow
          (kuratowskiMeasureNoncompactnessToEventFlow x) =
        kuratowskiMeasureNoncompactnessFromEventFlow
          (kuratowskiMeasureNoncompactnessToEventFlow y) :=
    congrArg kuratowskiMeasureNoncompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_round_trip y)))

instance kuratowskiMeasureNoncompactnessBHistCarrier :
    BHistCarrier KuratowskiMeasureNoncompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiMeasureNoncompactnessToEventFlow
  fromEventFlow := kuratowskiMeasureNoncompactnessFromEventFlow

instance kuratowskiMeasureNoncompactnessChapterTasteGate :
    ChapterTasteGate KuratowskiMeasureNoncompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiMeasureNoncompactnessFromEventFlow
      (kuratowskiMeasureNoncompactnessToEventFlow x) = some x
    exact KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kuratowskiMeasureNoncompactnessDecodeBHist
        (kuratowskiMeasureNoncompactnessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KuratowskiMeasureNoncompactnessUp) ∧
        Nonempty (ChapterTasteGate KuratowskiMeasureNoncompactnessUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KuratowskiMeasureNoncompactnessTasteGate_single_carrier_alignment_decode_encode,
      ⟨kuratowskiMeasureNoncompactnessBHistCarrier⟩,
      ⟨kuratowskiMeasureNoncompactnessChapterTasteGate⟩⟩

end BEDC.Derived.KuratowskiMeasureNoncompactnessUp
