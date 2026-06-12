import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactModulusOscillationRouterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactModulusOscillationRouterUp : Type where
  | mk
      (compact compactMetric continuity oscillation modulus dyadic regular real uniform
        transport replay provenance name : BHist) :
      CompactModulusOscillationRouterUp
  deriving DecidableEq

def compactModulusOscillationRouterEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactModulusOscillationRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactModulusOscillationRouterEncodeBHist h

def compactModulusOscillationRouterDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactModulusOscillationRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactModulusOscillationRouterDecodeBHist tail)

private theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactModulusOscillationRouterFields :
    CompactModulusOscillationRouterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactModulusOscillationRouterUp.mk compact compactMetric continuity oscillation modulus
      dyadic regular real uniform transport replay provenance name =>
      [compact, compactMetric, continuity, oscillation, modulus, dyadic, regular, real, uniform,
        transport, replay, provenance, name]

def compactModulusOscillationRouterToEventFlow :
    CompactModulusOscillationRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactModulusOscillationRouterFields x).map
      compactModulusOscillationRouterEncodeBHist

private def compactModulusOscillationRouterEventAtDefault :
    Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactModulusOscillationRouterEventAtDefault index rest

def compactModulusOscillationRouterFromEventFlow :
    EventFlow → Option CompactModulusOscillationRouterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactModulusOscillationRouterUp.mk
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 0 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 1 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 2 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 3 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 4 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 5 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 6 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 7 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 8 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 9 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 10 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 11 ef))
        (compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEventAtDefault 12 ef)))

private theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip
    (x : CompactModulusOscillationRouterUp) :
    compactModulusOscillationRouterFromEventFlow
        (compactModulusOscillationRouterToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk compact compactMetric continuity oscillation modulus dyadic regular real uniform
      transport replay provenance name =>
      change
        some
            (CompactModulusOscillationRouterUp.mk
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist compact))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist compactMetric))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist continuity))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist oscillation))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist modulus))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist dyadic))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist regular))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist real))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist uniform))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist transport))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist replay))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist provenance))
              (compactModulusOscillationRouterDecodeBHist
                (compactModulusOscillationRouterEncodeBHist name))) =
          some
            (CompactModulusOscillationRouterUp.mk compact compactMetric continuity
              oscillation modulus dyadic regular real uniform transport replay provenance name)
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode compact]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode compactMetric]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode continuity]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode oscillation]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode modulus]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode dyadic]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode regular]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode real]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode uniform]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode transport]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode replay]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode provenance]
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode name]

private theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment_injective
    {x y : CompactModulusOscillationRouterUp} :
    compactModulusOscillationRouterToEventFlow x =
      compactModulusOscillationRouterToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactModulusOscillationRouterFromEventFlow
          (compactModulusOscillationRouterToEventFlow x) =
        compactModulusOscillationRouterFromEventFlow
          (compactModulusOscillationRouterToEventFlow y) :=
    congrArg compactModulusOscillationRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip y)))

instance compactModulusOscillationRouterBHistCarrier :
    BHistCarrier CompactModulusOscillationRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactModulusOscillationRouterToEventFlow
  fromEventFlow := compactModulusOscillationRouterFromEventFlow

instance compactModulusOscillationRouterChapterTasteGate :
    ChapterTasteGate CompactModulusOscillationRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactModulusOscillationRouterFromEventFlow
          (compactModulusOscillationRouterToEventFlow x) =
        some x
    exact CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactModulusOscillationRouterTasteGate_single_carrier_alignment_injective heq)

theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        compactModulusOscillationRouterDecodeBHist
            (compactModulusOscillationRouterEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier CompactModulusOscillationRouterUp) ∧
        Nonempty (ChapterTasteGate CompactModulusOscillationRouterUp) ∧
          compactModulusOscillationRouterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode,
      ⟨⟨compactModulusOscillationRouterBHistCarrier⟩,
        ⟨⟨compactModulusOscillationRouterChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.CompactModulusOscillationRouterUp
