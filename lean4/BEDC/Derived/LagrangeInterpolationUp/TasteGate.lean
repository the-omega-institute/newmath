import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LagrangeInterpolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LagrangeInterpolationUp : Type where
  | mk :
      (nodes values denominators basis evaluation uniqueness transport replay provenance
        localCert : BHist) →
      LagrangeInterpolationUp
  deriving DecidableEq

def lagrangeInterpolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lagrangeInterpolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lagrangeInterpolationEncodeBHist h

def lagrangeInterpolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lagrangeInterpolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lagrangeInterpolationDecodeBHist tail)

theorem LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lagrangeInterpolationFields : LagrangeInterpolationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LagrangeInterpolationUp.mk nodes values denominators basis evaluation uniqueness transport
      replay provenance localCert =>
      [nodes, values, denominators, basis, evaluation, uniqueness, transport, replay,
        provenance, localCert]

def lagrangeInterpolationToEventFlow : LagrangeInterpolationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map lagrangeInterpolationEncodeBHist (lagrangeInterpolationFields x)

private def LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault index rest

def lagrangeInterpolationFromEventFlow : EventFlow → Option LagrangeInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LagrangeInterpolationUp.mk
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (lagrangeInterpolationDecodeBHist
          (LagrangeInterpolationTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

theorem LagrangeInterpolationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LagrangeInterpolationUp,
      lagrangeInterpolationFromEventFlow (lagrangeInterpolationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk nodes values denominators basis evaluation uniqueness transport replay provenance
      localCert =>
      change
        some
          (LagrangeInterpolationUp.mk
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist nodes))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist values))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist denominators))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist basis))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist evaluation))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist uniqueness))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist transport))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist replay))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist provenance))
            (lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist localCert))) =
          some
            (LagrangeInterpolationUp.mk nodes values denominators basis evaluation uniqueness
              transport replay provenance localCert)
      rw [LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode nodes,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode values,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode denominators,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode basis,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode evaluation,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode uniqueness,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode transport,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode replay,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode provenance,
        LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode localCert]

theorem LagrangeInterpolationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LagrangeInterpolationUp} :
    lagrangeInterpolationToEventFlow x = lagrangeInterpolationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lagrangeInterpolationFromEventFlow (lagrangeInterpolationToEventFlow x) =
        lagrangeInterpolationFromEventFlow (lagrangeInterpolationToEventFlow y) :=
    congrArg lagrangeInterpolationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LagrangeInterpolationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LagrangeInterpolationTasteGate_single_carrier_alignment_round_trip y)))

instance lagrangeInterpolationBHistCarrier : BHistCarrier LagrangeInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lagrangeInterpolationToEventFlow
  fromEventFlow := lagrangeInterpolationFromEventFlow

instance lagrangeInterpolationChapterTasteGate : ChapterTasteGate LagrangeInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lagrangeInterpolationFromEventFlow (lagrangeInterpolationToEventFlow x) = some x
    exact LagrangeInterpolationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LagrangeInterpolationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lagrangeInterpolationNontrivial : BEDC.Meta.TasteGate.Nontrivial LagrangeInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LagrangeInterpolationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LagrangeInterpolationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LagrangeInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lagrangeInterpolationChapterTasteGate

theorem LagrangeInterpolationTasteGate_single_carrier_alignment :
    (∀ h : BHist, lagrangeInterpolationDecodeBHist (lagrangeInterpolationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LagrangeInterpolationUp) ∧
        Nonempty (ChapterTasteGate LagrangeInterpolationUp) ∧
          lagrangeInterpolationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LagrangeInterpolationTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact Nonempty.intro lagrangeInterpolationBHistCarrier
    · constructor
      · exact Nonempty.intro lagrangeInterpolationChapterTasteGate
      · rfl

end BEDC.Derived.LagrangeInterpolationUp
