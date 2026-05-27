import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelPartialSummationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelPartialSummationUp : Type where
  | mk (R A S Delta B W Q D E H C P N : BHist) : AbelPartialSummationUp
  deriving DecidableEq

def abelPartialSummationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelPartialSummationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelPartialSummationEncodeBHist h

def abelPartialSummationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelPartialSummationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelPartialSummationDecodeBHist tail)

private theorem AbelPartialSummationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def abelPartialSummationFields : AbelPartialSummationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelPartialSummationUp.mk R A S Delta B W Q D E H C P N =>
      [R, A, S, Delta, B, W, Q, D, E, H, C, P, N]

def abelPartialSummationToEventFlow : AbelPartialSummationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (abelPartialSummationFields x).map abelPartialSummationEncodeBHist

private def abelPartialSummationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelPartialSummationEventAtDefault index rest

def abelPartialSummationFromEventFlow (ef : EventFlow) : Option AbelPartialSummationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelPartialSummationUp.mk
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 0 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 1 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 2 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 3 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 4 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 5 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 6 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 7 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 8 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 9 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 10 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 11 ef))
      (abelPartialSummationDecodeBHist (abelPartialSummationEventAtDefault 12 ef)))

private theorem AbelPartialSummationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AbelPartialSummationUp,
      abelPartialSummationFromEventFlow (abelPartialSummationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A S Delta B W Q D E H C P N =>
      change
        some
          (AbelPartialSummationUp.mk
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist R))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist A))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist S))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist Delta))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist B))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist W))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist Q))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist D))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist E))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist H))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist C))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist P))
            (abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist N))) =
          some (AbelPartialSummationUp.mk R A S Delta B W Q D E H C P N)
      rw [AbelPartialSummationTasteGate_single_carrier_alignment_decode R,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode A,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode S,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode Delta,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode B,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode W,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode Q,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode D,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode E,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode H,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode C,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode P,
        AbelPartialSummationTasteGate_single_carrier_alignment_decode N]

private theorem AbelPartialSummationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelPartialSummationUp} :
    abelPartialSummationToEventFlow x = abelPartialSummationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelPartialSummationFromEventFlow (abelPartialSummationToEventFlow x) =
        abelPartialSummationFromEventFlow (abelPartialSummationToEventFlow y) :=
    congrArg abelPartialSummationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AbelPartialSummationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelPartialSummationTasteGate_single_carrier_alignment_round_trip y)))

private theorem AbelPartialSummationTasteGate_single_carrier_alignment_fields :
    ∀ x y : AbelPartialSummationUp,
      abelPartialSummationFields x = abelPartialSummationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 A1 S1 Delta1 B1 W1 Q1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 A2 S2 Delta2 B2 W2 Q2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance abelPartialSummationBHistCarrier : BHistCarrier AbelPartialSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelPartialSummationToEventFlow
  fromEventFlow := abelPartialSummationFromEventFlow

instance abelPartialSummationChapterTasteGate : ChapterTasteGate AbelPartialSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelPartialSummationFromEventFlow (abelPartialSummationToEventFlow x) = some x
    exact AbelPartialSummationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelPartialSummationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance abelPartialSummationFieldFaithful : FieldFaithful AbelPartialSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := abelPartialSummationFields
  field_faithful := AbelPartialSummationTasteGate_single_carrier_alignment_fields

instance abelPartialSummationNontrivial : Nontrivial AbelPartialSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbelPartialSummationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AbelPartialSummationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AbelPartialSummationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelPartialSummationChapterTasteGate

theorem AbelPartialSummationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AbelPartialSummationUp) ∧
      Nonempty (FieldFaithful AbelPartialSummationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AbelPartialSummationUp) ∧
          (∀ h : BHist,
            abelPartialSummationDecodeBHist (abelPartialSummationEncodeBHist h) = h) ∧
            (∀ x : AbelPartialSummationUp,
              abelPartialSummationFromEventFlow (abelPartialSummationToEventFlow x) = some x) ∧
              abelPartialSummationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨abelPartialSummationChapterTasteGate⟩,
      ⟨abelPartialSummationFieldFaithful⟩,
      ⟨abelPartialSummationNontrivial⟩,
      AbelPartialSummationTasteGate_single_carrier_alignment_decode,
      AbelPartialSummationTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.AbelPartialSummationUp
