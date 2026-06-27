import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiClosureAxiomUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiClosureAxiomUp : Type where
  | mk (T S L E M I U H C P N : BHist) : KuratowskiClosureAxiomUp
  deriving DecidableEq

def kuratowskiClosureAxiomEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiClosureAxiomEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiClosureAxiomEncodeBHist h

def kuratowskiClosureAxiomDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiClosureAxiomDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiClosureAxiomDecodeBHist tail)

private theorem KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiClosureAxiomFields : KuratowskiClosureAxiomUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiClosureAxiomUp.mk T S L E M I U H C P N => [T, S, L, E, M, I, U, H, C, P, N]

def kuratowskiClosureAxiomToEventFlow : KuratowskiClosureAxiomUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kuratowskiClosureAxiomFields x).map kuratowskiClosureAxiomEncodeBHist

private def kuratowskiClosureAxiomEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kuratowskiClosureAxiomEventAt index rest

def kuratowskiClosureAxiomFromEventFlow
    (ef : EventFlow) : Option KuratowskiClosureAxiomUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KuratowskiClosureAxiomUp.mk
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 0 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 1 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 2 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 3 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 4 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 5 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 6 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 7 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 8 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 9 ef))
      (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEventAt 10 ef)))

private theorem KuratowskiClosureAxiomTasteGate_single_carrier_alignment_round_trip
    (x : KuratowskiClosureAxiomUp) :
    kuratowskiClosureAxiomFromEventFlow (kuratowskiClosureAxiomToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T S L E M I U H C P N =>
      change
        some
          (KuratowskiClosureAxiomUp.mk
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist T))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist S))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist L))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist E))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist M))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist I))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist U))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist H))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist C))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist P))
            (kuratowskiClosureAxiomDecodeBHist (kuratowskiClosureAxiomEncodeBHist N))) =
          some (KuratowskiClosureAxiomUp.mk T S L E M I U H C P N)
      rw [KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode T,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode S,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode L,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode E,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode M,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode I,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode U,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode H,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode C,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode P,
        KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode N]

private theorem KuratowskiClosureAxiomTasteGate_single_carrier_alignment_fields :
    ∀ x y : KuratowskiClosureAxiomUp,
      kuratowskiClosureAxiomFields x = kuratowskiClosureAxiomFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ S₁ L₁ E₁ M₁ I₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ S₂ L₂ E₂ M₂ I₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance kuratowskiClosureAxiomBHistCarrier : BHistCarrier KuratowskiClosureAxiomUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiClosureAxiomToEventFlow
  fromEventFlow := kuratowskiClosureAxiomFromEventFlow

instance kuratowskiClosureAxiomFieldFaithful : FieldFaithful KuratowskiClosureAxiomUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kuratowskiClosureAxiomFields
  field_faithful := KuratowskiClosureAxiomTasteGate_single_carrier_alignment_fields

instance kuratowskiClosureAxiomChapterTasteGate :
    ChapterTasteGate KuratowskiClosureAxiomUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiClosureAxiomFromEventFlow (kuratowskiClosureAxiomToEventFlow x) = some x
    exact KuratowskiClosureAxiomTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    have hread :
        kuratowskiClosureAxiomFromEventFlow (kuratowskiClosureAxiomToEventFlow x) =
          kuratowskiClosureAxiomFromEventFlow (kuratowskiClosureAxiomToEventFlow y) :=
      congrArg kuratowskiClosureAxiomFromEventFlow heq
    exact hxy
      (Option.some.inj
        (Eq.trans
          (KuratowskiClosureAxiomTasteGate_single_carrier_alignment_round_trip x).symm
          (Eq.trans hread
            (KuratowskiClosureAxiomTasteGate_single_carrier_alignment_round_trip y))))

instance kuratowskiClosureAxiomNontrivial : Nontrivial KuratowskiClosureAxiomUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KuratowskiClosureAxiomUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KuratowskiClosureAxiomUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem KuratowskiClosureAxiomTasteGate_single_carrier_alignment :
    (∀ h : BHist, kuratowskiClosureAxiomDecodeBHist
      (kuratowskiClosureAxiomEncodeBHist h) = h) ∧
      (∀ x : KuratowskiClosureAxiomUp,
        kuratowskiClosureAxiomFromEventFlow (kuratowskiClosureAxiomToEventFlow x) = some x) ∧
      (∀ x y : KuratowskiClosureAxiomUp,
        kuratowskiClosureAxiomToEventFlow x = kuratowskiClosureAxiomToEventFlow y → x = y) ∧
      kuratowskiClosureAxiomEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact KuratowskiClosureAxiomTasteGate_single_carrier_alignment_decode
  · constructor
    · exact KuratowskiClosureAxiomTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        have hread :
            kuratowskiClosureAxiomFromEventFlow (kuratowskiClosureAxiomToEventFlow x) =
              kuratowskiClosureAxiomFromEventFlow (kuratowskiClosureAxiomToEventFlow y) :=
          congrArg kuratowskiClosureAxiomFromEventFlow heq
        exact Option.some.inj
          (Eq.trans
            (KuratowskiClosureAxiomTasteGate_single_carrier_alignment_round_trip x).symm
            (Eq.trans hread
              (KuratowskiClosureAxiomTasteGate_single_carrier_alignment_round_trip y)))
      · rfl

end BEDC.Derived.KuratowskiClosureAxiomUp
