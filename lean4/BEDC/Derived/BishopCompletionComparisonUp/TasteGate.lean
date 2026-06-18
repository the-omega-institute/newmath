import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionComparisonUp : Type where
  | mk
      (regularSource boundary locatedLimit locatedReal realSeal transport replay provenance
        name : BHist) :
      BishopCompletionComparisonUp
  deriving DecidableEq

def bishopCompletionComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionComparisonEncodeBHist h

def bishopCompletionComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionComparisonDecodeBHist tail)

private theorem BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BishopCompletionComparisonTasteGate_single_carrier_alignment_fields :
    BishopCompletionComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionComparisonUp.mk regularSource boundary locatedLimit locatedReal realSeal
      transport replay provenance name =>
      [regularSource, boundary, locatedLimit, locatedReal, realSeal, transport, replay,
        provenance, name]

def BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow :
    BishopCompletionComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BishopCompletionComparisonTasteGate_single_carrier_alignment_fields x).map
      bishopCompletionComparisonEncodeBHist

private def bishopCompletionComparisonEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionComparisonEventAt index rest

def BishopCompletionComparisonTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BishopCompletionComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    some
      (BishopCompletionComparisonUp.mk
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 0 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 1 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 2 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 3 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 4 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 5 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 6 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 7 eventFlow))
        (bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEventAt 8 eventFlow)))

instance bishopCompletionComparisonBHistCarrier :
    BHistCarrier BishopCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BishopCompletionComparisonTasteGate_single_carrier_alignment_fromEventFlow

private theorem BishopCompletionComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCompletionComparisonUp,
      BishopCompletionComparisonTasteGate_single_carrier_alignment_fromEventFlow
        (BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk regularSource boundary locatedLimit locatedReal realSeal transport replay provenance
      name =>
      change
        some
            (BishopCompletionComparisonUp.mk
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist regularSource))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist boundary))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist locatedLimit))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist locatedReal))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist realSeal))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist transport))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist replay))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist provenance))
              (bishopCompletionComparisonDecodeBHist
                (bishopCompletionComparisonEncodeBHist name))) =
          some
            (BishopCompletionComparisonUp.mk regularSource boundary locatedLimit locatedReal
              realSeal transport replay provenance name)
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode
        regularSource]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode boundary]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode
        locatedLimit]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode
        locatedReal]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode realSeal]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode
        transport]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode replay]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode
        provenance]
      rw [BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode name]

private theorem BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompletionComparisonUp} :
    BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow x =
      BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BishopCompletionComparisonTasteGate_single_carrier_alignment_fromEventFlow
          (BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow x) =
        BishopCompletionComparisonTasteGate_single_carrier_alignment_fromEventFlow
          (BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BishopCompletionComparisonTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCompletionComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCompletionComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCompletionComparisonChapterTasteGate :
    ChapterTasteGate BishopCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BishopCompletionComparisonTasteGate_single_carrier_alignment_fromEventFlow
        (BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
    exact BishopCompletionComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopCompletionComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCompletionComparisonDecodeBHist (bishopCompletionComparisonEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopCompletionComparisonUp) ∧
      Nonempty (ChapterTasteGate BishopCompletionComparisonUp) ∧
      bishopCompletionComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopCompletionComparisonTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨bishopCompletionComparisonBHistCarrier⟩,
        ⟨⟨bishopCompletionComparisonChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.BishopCompletionComparisonUp
