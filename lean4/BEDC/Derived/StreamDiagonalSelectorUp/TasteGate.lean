import BEDC.Derived.StreamDiagonalSelectorUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamDiagonalSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamDiagonalSelectorUp : Type where
  | mk
      (schedule selector window readback dyadicLedger diagonalPacket routes provenance
        nameCert : BHist) : StreamDiagonalSelectorUp
  deriving DecidableEq

def streamDiagonalSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamDiagonalSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamDiagonalSelectorEncodeBHist h

def streamDiagonalSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamDiagonalSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamDiagonalSelectorDecodeBHist tail)

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def streamDiagonalSelectorFields : StreamDiagonalSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamDiagonalSelectorUp.mk schedule selector window readback dyadicLedger diagonalPacket
      routes provenance nameCert =>
      [schedule, selector, window, readback, dyadicLedger, diagonalPacket, routes, provenance,
        nameCert]

def streamDiagonalSelectorToEventFlow : StreamDiagonalSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (streamDiagonalSelectorFields x).map streamDiagonalSelectorEncodeBHist

private def streamDiagonalSelectorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => streamDiagonalSelectorEventAt index rest

def streamDiagonalSelectorFromEventFlow (ef : EventFlow) : Option StreamDiagonalSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StreamDiagonalSelectorUp.mk
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 0 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 1 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 2 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 3 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 4 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 5 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 6 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 7 ef))
      (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEventAt 8 ef)))

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip
    (x : StreamDiagonalSelectorUp) :
    streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert =>
      change
        some
          (StreamDiagonalSelectorUp.mk
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist schedule))
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist selector))
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist window))
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist readback))
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist dyadicLedger))
            (streamDiagonalSelectorDecodeBHist
              (streamDiagonalSelectorEncodeBHist diagonalPacket))
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist routes))
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist provenance))
            (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist nameCert))) =
          some
            (StreamDiagonalSelectorUp.mk schedule selector window readback dyadicLedger
              diagonalPacket routes provenance nameCert)
      rw [StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode schedule,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode selector,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode window,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode readback,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode diagonalPacket,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode routes,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode provenance,
        StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StreamDiagonalSelectorUp} :
    streamDiagonalSelectorToEventFlow x = streamDiagonalSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) =
        streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow y) :=
    congrArg streamDiagonalSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip y)))

instance StreamDiagonalSelectorTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamDiagonalSelectorToEventFlow
  fromEventFlow := streamDiagonalSelectorFromEventFlow

instance StreamDiagonalSelectorTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x
    exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StreamDiagonalSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def StreamDiagonalSelectorTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate StreamDiagonalSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  StreamDiagonalSelectorTasteGate_single_carrier_alignment_ChapterTasteGate

theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment :
    Nonempty StreamDiagonalSelectorUp ∧
      (∃ x : StreamDiagonalSelectorUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
          streamDiagonalSelectorEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            streamDiagonalSelectorEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1]) := by
  -- BEDC touchpoint anchor: BHist BMark
  let x :=
    StreamDiagonalSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  constructor
  · exact ⟨x⟩
  · refine ⟨x, ?_, rfl, rfl⟩
    change streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x
    exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip x

end BEDC.Derived.StreamDiagonalSelectorUp
