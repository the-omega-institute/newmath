import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformOscillationUp : Type where
  | mk
      (compact continuous modulus distance witness transport replay provenance localName :
        BHist) : CompactUniformOscillationUp
  deriving DecidableEq

def compactUniformOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformOscillationEncodeBHist h

def compactUniformOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformOscillationDecodeBHist tail)

private theorem compactUniformOscillation_decode_encode :
    ∀ h : BHist,
      compactUniformOscillationDecodeBHist
        (compactUniformOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactUniformOscillationFields :
    CompactUniformOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformOscillationUp.mk compact continuous modulus distance witness transport
      replay provenance localName =>
      [compact, continuous, modulus, distance, witness, transport, replay, provenance,
        localName]

def compactUniformOscillationToEventFlow :
    CompactUniformOscillationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactUniformOscillationFields x).map compactUniformOscillationEncodeBHist

private def compactUniformOscillationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformOscillationEventAtDefault index rest

def compactUniformOscillationFromEventFlow
    (ef : EventFlow) : Option CompactUniformOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformOscillationUp.mk
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 0 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 1 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 2 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 3 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 4 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 5 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 6 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 7 ef))
      (compactUniformOscillationDecodeBHist
        (compactUniformOscillationEventAtDefault 8 ef)))

private theorem compactUniformOscillation_round_trip
    (x : CompactUniformOscillationUp) :
    compactUniformOscillationFromEventFlow
      (compactUniformOscillationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk compact continuous modulus distance witness transport replay provenance localName =>
      change
        some
          (CompactUniformOscillationUp.mk
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist compact))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist continuous))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist modulus))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist distance))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist witness))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist transport))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist replay))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist provenance))
            (compactUniformOscillationDecodeBHist
              (compactUniformOscillationEncodeBHist localName))) =
          some
            (CompactUniformOscillationUp.mk compact continuous modulus distance witness
              transport replay provenance localName)
      rw [compactUniformOscillation_decode_encode compact,
        compactUniformOscillation_decode_encode continuous,
        compactUniformOscillation_decode_encode modulus,
        compactUniformOscillation_decode_encode distance,
        compactUniformOscillation_decode_encode witness,
        compactUniformOscillation_decode_encode transport,
        compactUniformOscillation_decode_encode replay,
        compactUniformOscillation_decode_encode provenance,
        compactUniformOscillation_decode_encode localName]

private theorem compactUniformOscillationToEventFlow_injective
    {x y : CompactUniformOscillationUp} :
    compactUniformOscillationToEventFlow x =
      compactUniformOscillationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformOscillationFromEventFlow
          (compactUniformOscillationToEventFlow x) =
        compactUniformOscillationFromEventFlow
          (compactUniformOscillationToEventFlow y) :=
    congrArg compactUniformOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformOscillation_round_trip x).symm
      (Eq.trans hread (compactUniformOscillation_round_trip y)))

instance compactUniformOscillationBHistCarrier :
    BHistCarrier CompactUniformOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformOscillationToEventFlow
  fromEventFlow := compactUniformOscillationFromEventFlow

instance compactUniformOscillationChapterTasteGate :
    ChapterTasteGate CompactUniformOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformOscillationFromEventFlow
        (compactUniformOscillationToEventFlow x) = some x
    exact compactUniformOscillation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformOscillationToEventFlow_injective heq)

theorem CompactUniformOscillationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactUniformOscillationUp) ∧
      (∀ h : BHist,
        compactUniformOscillationDecodeBHist
          (compactUniformOscillationEncodeBHist h) = h) ∧
        compactUniformOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨compactUniformOscillationChapterTasteGate⟩,
      compactUniformOscillation_decode_encode,
      rfl⟩

end BEDC.Derived.CompactUniformOscillationUp
