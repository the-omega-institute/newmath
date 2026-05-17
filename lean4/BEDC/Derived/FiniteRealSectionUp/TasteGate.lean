import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRealSectionUp : Type where
  | mk (q W R D E H C P N : BHist) : FiniteRealSectionUp
  deriving DecidableEq

def finiteRealSectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRealSectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRealSectionEncodeBHist h

def finiteRealSectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRealSectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRealSectionDecodeBHist tail)

private theorem FiniteRealSectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRealSectionToEventFlow : FiniteRealSectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRealSectionUp.mk q W R D E H C P N =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        finiteRealSectionEncodeBHist q,
        finiteRealSectionEncodeBHist W,
        finiteRealSectionEncodeBHist R,
        finiteRealSectionEncodeBHist D,
        finiteRealSectionEncodeBHist E,
        finiteRealSectionEncodeBHist H,
        finiteRealSectionEncodeBHist C,
        finiteRealSectionEncodeBHist P,
        finiteRealSectionEncodeBHist N]

private def finiteRealSectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteRealSectionEventAtDefault index rest

def finiteRealSectionFromEventFlow (ef : EventFlow) : Option FiniteRealSectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteRealSectionUp.mk
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 1 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 2 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 3 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 4 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 5 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 6 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 7 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 8 ef))
      (finiteRealSectionDecodeBHist (finiteRealSectionEventAtDefault 9 ef)))

private theorem FiniteRealSectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteRealSectionUp,
      finiteRealSectionFromEventFlow (finiteRealSectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q W R D E H C P N =>
      change
        some
          (FiniteRealSectionUp.mk
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist q))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist W))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist R))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist D))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist E))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist H))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist C))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist P))
            (finiteRealSectionDecodeBHist (finiteRealSectionEncodeBHist N))) =
          some (FiniteRealSectionUp.mk q W R D E H C P N)
      rw [FiniteRealSectionTasteGate_single_carrier_alignment_decode q,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode W,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode R,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode D,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode E,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode H,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode C,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode P,
        FiniteRealSectionTasteGate_single_carrier_alignment_decode N]

private theorem FiniteRealSectionTasteGate_single_carrier_alignment_injective
    {x y : FiniteRealSectionUp} :
    finiteRealSectionToEventFlow x = finiteRealSectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRealSectionFromEventFlow (finiteRealSectionToEventFlow x) =
        finiteRealSectionFromEventFlow (finiteRealSectionToEventFlow y) :=
    congrArg finiteRealSectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteRealSectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteRealSectionTasteGate_single_carrier_alignment_round_trip y)))

private def finiteRealSectionFields : FiniteRealSectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRealSectionUp.mk q W R D E H C P N => [q, W, R, D, E, H, C, P, N]

private theorem FiniteRealSectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteRealSectionUp,
      finiteRealSectionFields x = finiteRealSectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q1 W1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk q2 W2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteRealSectionBHistCarrier : BHistCarrier FiniteRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRealSectionToEventFlow
  fromEventFlow := finiteRealSectionFromEventFlow

instance finiteRealSectionChapterTasteGate : ChapterTasteGate FiniteRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteRealSectionFromEventFlow (finiteRealSectionToEventFlow x) = some x
    exact FiniteRealSectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteRealSectionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FiniteRealSectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRealSectionChapterTasteGate

instance finiteRealSectionFieldFaithful : FieldFaithful FiniteRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteRealSectionFields
  field_faithful := FiniteRealSectionTasteGate_single_carrier_alignment_fields

instance finiteRealSectionNontrivial : Nontrivial FiniteRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteRealSectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteRealSectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteRealSectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteRealSectionUp) ∧
      (∀ x : FiniteRealSectionUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (BHistCarrier.toEventFlow
            (FiniteRealSectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b0, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [], []]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨finiteRealSectionChapterTasteGate⟩
  · constructor
    · intro x
      change finiteRealSectionFromEventFlow (finiteRealSectionToEventFlow x) = some x
      exact FiniteRealSectionTasteGate_single_carrier_alignment_round_trip x
    · rfl

end BEDC.Derived.FiniteRealSectionUp
