import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelSummationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelSummationUp : Type where
  | mk (S A D B T R E H C P N : BHist) : AbelSummationUp
  deriving DecidableEq

def abelSummationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelSummationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelSummationEncodeBHist h

def abelSummationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelSummationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelSummationDecodeBHist tail)

private theorem AbelSummationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, abelSummationDecodeBHist (abelSummationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def abelSummationToEventFlow : AbelSummationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AbelSummationUp.mk S A D B T R E H C P N =>
      [[BMark.b0],
        abelSummationEncodeBHist S,
        [BMark.b1, BMark.b0],
        abelSummationEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        abelSummationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelSummationEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelSummationEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelSummationEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelSummationEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        abelSummationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        abelSummationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        abelSummationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelSummationEncodeBHist N]

private def abelSummationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelSummationEventAtDefault index rest

def abelSummationFromEventFlow (ef : EventFlow) : Option AbelSummationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelSummationUp.mk
      (abelSummationDecodeBHist (abelSummationEventAtDefault 1 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 3 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 5 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 7 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 9 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 11 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 13 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 15 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 17 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 19 ef))
      (abelSummationDecodeBHist (abelSummationEventAtDefault 21 ef)))

private theorem AbelSummationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AbelSummationUp,
      abelSummationFromEventFlow (abelSummationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A D B T R E H C P N =>
      change
        some
          (AbelSummationUp.mk
            (abelSummationDecodeBHist (abelSummationEncodeBHist S))
            (abelSummationDecodeBHist (abelSummationEncodeBHist A))
            (abelSummationDecodeBHist (abelSummationEncodeBHist D))
            (abelSummationDecodeBHist (abelSummationEncodeBHist B))
            (abelSummationDecodeBHist (abelSummationEncodeBHist T))
            (abelSummationDecodeBHist (abelSummationEncodeBHist R))
            (abelSummationDecodeBHist (abelSummationEncodeBHist E))
            (abelSummationDecodeBHist (abelSummationEncodeBHist H))
            (abelSummationDecodeBHist (abelSummationEncodeBHist C))
            (abelSummationDecodeBHist (abelSummationEncodeBHist P))
            (abelSummationDecodeBHist (abelSummationEncodeBHist N))) =
          some (AbelSummationUp.mk S A D B T R E H C P N)
      rw [AbelSummationTasteGate_single_carrier_alignment_decode S,
        AbelSummationTasteGate_single_carrier_alignment_decode A,
        AbelSummationTasteGate_single_carrier_alignment_decode D,
        AbelSummationTasteGate_single_carrier_alignment_decode B,
        AbelSummationTasteGate_single_carrier_alignment_decode T,
        AbelSummationTasteGate_single_carrier_alignment_decode R,
        AbelSummationTasteGate_single_carrier_alignment_decode E,
        AbelSummationTasteGate_single_carrier_alignment_decode H,
        AbelSummationTasteGate_single_carrier_alignment_decode C,
        AbelSummationTasteGate_single_carrier_alignment_decode P,
        AbelSummationTasteGate_single_carrier_alignment_decode N]

private theorem AbelSummationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelSummationUp} :
    abelSummationToEventFlow x = abelSummationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelSummationFromEventFlow (abelSummationToEventFlow x) =
        abelSummationFromEventFlow (abelSummationToEventFlow y) :=
    congrArg abelSummationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AbelSummationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelSummationTasteGate_single_carrier_alignment_round_trip y)))

private def abelSummationFields : AbelSummationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelSummationUp.mk S A D B T R E H C P N => [S, A, D, B, T, R, E, H, C, P, N]

private theorem AbelSummationTasteGate_single_carrier_alignment_fields :
    ∀ x y : AbelSummationUp, abelSummationFields x = abelSummationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 A1 D1 B1 T1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 A2 D2 B2 T2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance abelSummationBHistCarrier : BHistCarrier AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelSummationToEventFlow
  fromEventFlow := abelSummationFromEventFlow

instance abelSummationChapterTasteGate : ChapterTasteGate AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelSummationFromEventFlow (abelSummationToEventFlow x) = some x
    exact AbelSummationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelSummationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance abelSummationFieldFaithful : FieldFaithful AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := abelSummationFields
  field_faithful := AbelSummationTasteGate_single_carrier_alignment_fields

instance abelSummationNontrivial : Nontrivial AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbelSummationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AbelSummationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AbelSummationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelSummationChapterTasteGate

theorem AbelSummationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AbelSummationUp) ∧
      Nonempty (FieldFaithful AbelSummationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AbelSummationUp) ∧
          (∀ h : BHist, abelSummationDecodeBHist (abelSummationEncodeBHist h) = h) ∧
            (∀ x : AbelSummationUp,
              abelSummationFromEventFlow (abelSummationToEventFlow x) = some x) ∧
              (∀ x y : AbelSummationUp,
                abelSummationToEventFlow x = abelSummationToEventFlow y → x = y) ∧
                abelSummationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨abelSummationChapterTasteGate⟩,
      ⟨abelSummationFieldFaithful⟩,
      ⟨abelSummationNontrivial⟩,
      AbelSummationTasteGate_single_carrier_alignment_decode,
      AbelSummationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => AbelSummationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AbelSummationUp
