import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformLocalToGlobalModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformLocalToGlobalModulusUp : Type where
  | mk
      (compactNet localModulus localRadius lowerBound triangle uniform transport replay
        provenance name : BHist) :
      CompactUniformLocalToGlobalModulusUp
  deriving DecidableEq

def compactUniformLocalToGlobalModulusEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformLocalToGlobalModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformLocalToGlobalModulusEncodeBHist h

def compactUniformLocalToGlobalModulusDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformLocalToGlobalModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformLocalToGlobalModulusDecodeBHist tail)

private theorem CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformLocalToGlobalModulusFields :
    CompactUniformLocalToGlobalModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformLocalToGlobalModulusUp.mk compactNet localModulus localRadius lowerBound
      triangle uniform transport replay provenance name =>
      [compactNet, localModulus, localRadius, lowerBound, triangle, uniform, transport,
        replay, provenance, name]

def compactUniformLocalToGlobalModulusToEventFlow :
    CompactUniformLocalToGlobalModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformLocalToGlobalModulusFields x).map
      compactUniformLocalToGlobalModulusEncodeBHist

private def compactUniformLocalToGlobalModulusEventAtDefault :
    Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformLocalToGlobalModulusEventAtDefault index rest

def compactUniformLocalToGlobalModulusFromEventFlow :
    EventFlow → Option CompactUniformLocalToGlobalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactUniformLocalToGlobalModulusUp.mk
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 0 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 1 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 2 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 3 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 4 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 5 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 6 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 7 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 8 ef))
        (compactUniformLocalToGlobalModulusDecodeBHist
          (compactUniformLocalToGlobalModulusEventAtDefault 9 ef)))

private theorem CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_round_trip
    (x : CompactUniformLocalToGlobalModulusUp) :
    compactUniformLocalToGlobalModulusFromEventFlow
        (compactUniformLocalToGlobalModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk compactNet localModulus localRadius lowerBound triangle uniform transport replay
      provenance name =>
      change
        some
            (CompactUniformLocalToGlobalModulusUp.mk
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist compactNet))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist localModulus))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist localRadius))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist lowerBound))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist triangle))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist uniform))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist transport))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist replay))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist provenance))
              (compactUniformLocalToGlobalModulusDecodeBHist
                (compactUniformLocalToGlobalModulusEncodeBHist name))) =
          some
            (CompactUniformLocalToGlobalModulusUp.mk compactNet localModulus localRadius
              lowerBound triangle uniform transport replay provenance name)
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode compactNet]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode localModulus]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode localRadius]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode lowerBound]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode triangle]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode uniform]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode transport]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode replay]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode provenance]
      rw [CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode name]

private theorem CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_injective
    {x y : CompactUniformLocalToGlobalModulusUp} :
    compactUniformLocalToGlobalModulusToEventFlow x =
      compactUniformLocalToGlobalModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformLocalToGlobalModulusFromEventFlow
          (compactUniformLocalToGlobalModulusToEventFlow x) =
        compactUniformLocalToGlobalModulusFromEventFlow
          (compactUniformLocalToGlobalModulusToEventFlow y) :=
    congrArg compactUniformLocalToGlobalModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformLocalToGlobalModulusBHistCarrier :
    BHistCarrier CompactUniformLocalToGlobalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformLocalToGlobalModulusToEventFlow
  fromEventFlow := compactUniformLocalToGlobalModulusFromEventFlow

instance compactUniformLocalToGlobalModulusChapterTasteGate :
    ChapterTasteGate CompactUniformLocalToGlobalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformLocalToGlobalModulusFromEventFlow
          (compactUniformLocalToGlobalModulusToEventFlow x) =
        some x
    exact CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_injective heq)

theorem CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        compactUniformLocalToGlobalModulusDecodeBHist
            (compactUniformLocalToGlobalModulusEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier CompactUniformLocalToGlobalModulusUp) ∧
        Nonempty (ChapterTasteGate CompactUniformLocalToGlobalModulusUp) ∧
          compactUniformLocalToGlobalModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactUniformLocalToGlobalModulusTasteGate_single_carrier_alignment_decode,
      ⟨⟨compactUniformLocalToGlobalModulusBHistCarrier⟩,
        ⟨⟨compactUniformLocalToGlobalModulusChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.CompactUniformLocalToGlobalModulusUp
