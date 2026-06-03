import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletenessWitnessObligationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletenessWitnessObligationUp : Type where
  | mk (W A K R D S E H C P N : BHist) : CauchyCompletenessWitnessObligationUp
  deriving DecidableEq

def cauchyCompletenessWitnessObligationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletenessWitnessObligationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletenessWitnessObligationEncodeBHist h

def cauchyCompletenessWitnessObligationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletenessWitnessObligationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletenessWitnessObligationDecodeBHist tail)

private theorem CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletenessWitnessObligationDecodeBHist
          (cauchyCompletenessWitnessObligationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletenessWitnessObligationFields :
    CauchyCompletenessWitnessObligationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletenessWitnessObligationUp.mk W A K R D S E H C P N =>
      [W, A, K, R, D, S, E, H, C, P, N]

def cauchyCompletenessWitnessObligationToEventFlow :
    CauchyCompletenessWitnessObligationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletenessWitnessObligationFields x).map
        cauchyCompletenessWitnessObligationEncodeBHist

private def cauchyCompletenessWitnessObligationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletenessWitnessObligationEventAt index rest

def cauchyCompletenessWitnessObligationFromEventFlow
    (ef : EventFlow) : Option CauchyCompletenessWitnessObligationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletenessWitnessObligationUp.mk
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 0 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 1 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 2 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 3 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 4 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 5 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 6 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 7 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 8 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 9 ef))
      (cauchyCompletenessWitnessObligationDecodeBHist
        (cauchyCompletenessWitnessObligationEventAt 10 ef)))

private theorem CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletenessWitnessObligationUp) :
    cauchyCompletenessWitnessObligationFromEventFlow
        (cauchyCompletenessWitnessObligationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W A K R D S E H C P N =>
      change
        some
          (CauchyCompletenessWitnessObligationUp.mk
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist W))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist A))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist K))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist R))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist D))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist S))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist E))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist H))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist C))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist P))
            (cauchyCompletenessWitnessObligationDecodeBHist
              (cauchyCompletenessWitnessObligationEncodeBHist N))) =
          some (CauchyCompletenessWitnessObligationUp.mk W A K R D S E H C P N)
      rw [
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode W,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode A,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode K,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletenessWitnessObligationUp} :
    cauchyCompletenessWitnessObligationToEventFlow x =
        cauchyCompletenessWitnessObligationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletenessWitnessObligationFromEventFlow
          (cauchyCompletenessWitnessObligationToEventFlow x) =
        cauchyCompletenessWitnessObligationFromEventFlow
          (cauchyCompletenessWitnessObligationToEventFlow y) :=
    congrArg cauchyCompletenessWitnessObligationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyCompletenessWitnessObligationUp,
      cauchyCompletenessWitnessObligationFields x =
          cauchyCompletenessWitnessObligationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 A1 K1 R1 D1 S1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 A2 K2 R2 D2 S2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletenessWitnessObligationBHistCarrier :
    BHistCarrier CauchyCompletenessWitnessObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletenessWitnessObligationToEventFlow
  fromEventFlow := cauchyCompletenessWitnessObligationFromEventFlow

instance cauchyCompletenessWitnessObligationChapterTasteGate :
    ChapterTasteGate CauchyCompletenessWitnessObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletenessWitnessObligationFromEventFlow
          (cauchyCompletenessWitnessObligationToEventFlow x) =
        some x
    exact CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCompletenessWitnessObligationFieldFaithful :
    FieldFaithful CauchyCompletenessWitnessObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletenessWitnessObligationFields
  field_faithful :=
    CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_fields

instance cauchyCompletenessWitnessObligationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletenessWitnessObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletenessWitnessObligationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletenessWitnessObligationUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletenessWitnessObligationUp) ∧
      Nonempty (FieldFaithful CauchyCompletenessWitnessObligationUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyCompletenessWitnessObligationUp) ∧
      (∀ h : BHist,
        cauchyCompletenessWitnessObligationDecodeBHist
            (cauchyCompletenessWitnessObligationEncodeBHist h) =
          h) ∧
      (∀ x : CauchyCompletenessWitnessObligationUp,
        cauchyCompletenessWitnessObligationFromEventFlow
            (cauchyCompletenessWitnessObligationToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCompletenessWitnessObligationUp,
        cauchyCompletenessWitnessObligationToEventFlow x =
            cauchyCompletenessWitnessObligationToEventFlow y →
          x = y) ∧
      cauchyCompletenessWitnessObligationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyCompletenessWitnessObligationChapterTasteGate⟩,
      ⟨cauchyCompletenessWitnessObligationFieldFaithful⟩,
      ⟨cauchyCompletenessWitnessObligationNontrivial⟩,
      CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletenessWitnessObligationTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchyCompletenessWitnessObligationUp
