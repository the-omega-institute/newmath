import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedIntervalOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedIntervalOscillationUp : Type where
  | mk
      (interval graph windows readback dyadic oscillation realSeal transport replay provenance
        name : BHist) : BishopLocatedIntervalOscillationUp
  deriving DecidableEq

def bishopLocatedIntervalOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedIntervalOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedIntervalOscillationEncodeBHist h

def bishopLocatedIntervalOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedIntervalOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedIntervalOscillationDecodeBHist tail)

private theorem BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopLocatedIntervalOscillationDecodeBHist
          (bishopLocatedIntervalOscillationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedIntervalOscillationFields :
    BishopLocatedIntervalOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedIntervalOscillationUp.mk interval graph windows readback dyadic oscillation
      realSeal transport replay provenance name =>
      [interval, graph, windows, readback, dyadic, oscillation, realSeal, transport, replay,
        provenance, name]

def bishopLocatedIntervalOscillationToEventFlow :
    BishopLocatedIntervalOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedIntervalOscillationFields x).map
      bishopLocatedIntervalOscillationEncodeBHist

private def bishopLocatedIntervalOscillationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedIntervalOscillationEventAt index rest

def bishopLocatedIntervalOscillationFromEventFlow
    (ef : EventFlow) : Option BishopLocatedIntervalOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedIntervalOscillationUp.mk
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 0 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 1 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 2 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 3 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 4 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 5 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 6 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 7 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 8 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 9 ef))
      (bishopLocatedIntervalOscillationDecodeBHist
        (bishopLocatedIntervalOscillationEventAt 10 ef)))

private theorem BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_round_trip
    (x : BishopLocatedIntervalOscillationUp) :
    bishopLocatedIntervalOscillationFromEventFlow
        (bishopLocatedIntervalOscillationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk interval graph windows readback dyadic oscillation realSeal transport replay provenance
      name =>
      change
        some
            (BishopLocatedIntervalOscillationUp.mk
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist interval))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist graph))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist windows))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist readback))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist dyadic))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist oscillation))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist realSeal))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist transport))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist replay))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist provenance))
              (bishopLocatedIntervalOscillationDecodeBHist
                (bishopLocatedIntervalOscillationEncodeBHist name))) =
          some
            (BishopLocatedIntervalOscillationUp.mk interval graph windows readback dyadic
              oscillation realSeal transport replay provenance name)
      rw [
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode
          interval,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode graph,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode windows,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode readback,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode dyadic,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode
          oscillation,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode
          realSeal,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode
          transport,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode replay,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode
          provenance,
        BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode name]

private theorem BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedIntervalOscillationUp} :
    bishopLocatedIntervalOscillationToEventFlow x =
        bishopLocatedIntervalOscillationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedIntervalOscillationFromEventFlow
          (bishopLocatedIntervalOscillationToEventFlow x) =
        bishopLocatedIntervalOscillationFromEventFlow
          (bishopLocatedIntervalOscillationToEventFlow y) :=
    congrArg bishopLocatedIntervalOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedIntervalOscillationBHistCarrier :
    BHistCarrier BishopLocatedIntervalOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedIntervalOscillationToEventFlow
  fromEventFlow := bishopLocatedIntervalOscillationFromEventFlow

instance bishopLocatedIntervalOscillationChapterTasteGate :
    ChapterTasteGate BishopLocatedIntervalOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedIntervalOscillationFromEventFlow
          (bishopLocatedIntervalOscillationToEventFlow x) =
        some x
    exact BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_injective heq)

theorem BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopLocatedIntervalOscillationDecodeBHist
            (bishopLocatedIntervalOscillationEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier BishopLocatedIntervalOscillationUp) ∧
        Nonempty (ChapterTasteGate BishopLocatedIntervalOscillationUp) ∧
          bishopLocatedIntervalOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopLocatedIntervalOscillationTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨bishopLocatedIntervalOscillationBHistCarrier⟩,
        ⟨⟨bishopLocatedIntervalOscillationChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.BishopLocatedIntervalOscillationUp
