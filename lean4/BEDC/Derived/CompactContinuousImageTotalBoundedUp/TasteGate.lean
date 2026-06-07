import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactContinuousImageTotalBoundedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactContinuousImageTotalBoundedUp : Type where
  | mk (X F U M R B H C P N : BHist) : CompactContinuousImageTotalBoundedUp
  deriving DecidableEq

def compactContinuousImageTotalBoundedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactContinuousImageTotalBoundedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactContinuousImageTotalBoundedEncodeBHist h

def compactContinuousImageTotalBoundedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactContinuousImageTotalBoundedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactContinuousImageTotalBoundedDecodeBHist tail)

private theorem CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactContinuousImageTotalBoundedDecodeBHist
          (compactContinuousImageTotalBoundedEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactContinuousImageTotalBoundedToEventFlow :
    CompactContinuousImageTotalBoundedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactContinuousImageTotalBoundedUp.mk X F U M R B H C P N =>
      [compactContinuousImageTotalBoundedEncodeBHist X,
        compactContinuousImageTotalBoundedEncodeBHist F,
        compactContinuousImageTotalBoundedEncodeBHist U,
        compactContinuousImageTotalBoundedEncodeBHist M,
        compactContinuousImageTotalBoundedEncodeBHist R,
        compactContinuousImageTotalBoundedEncodeBHist B,
        compactContinuousImageTotalBoundedEncodeBHist H,
        compactContinuousImageTotalBoundedEncodeBHist C,
        compactContinuousImageTotalBoundedEncodeBHist P,
        compactContinuousImageTotalBoundedEncodeBHist N]

private def compactContinuousImageTotalBoundedEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactContinuousImageTotalBoundedEventAtDefault index rest

def compactContinuousImageTotalBoundedFromEventFlow
    (ef : EventFlow) : Option CompactContinuousImageTotalBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactContinuousImageTotalBoundedUp.mk
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 0 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 1 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 2 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 3 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 4 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 5 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 6 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 7 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 8 ef))
      (compactContinuousImageTotalBoundedDecodeBHist
        (compactContinuousImageTotalBoundedEventAtDefault 9 ef)))

private theorem CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactContinuousImageTotalBoundedUp,
      compactContinuousImageTotalBoundedFromEventFlow
          (compactContinuousImageTotalBoundedToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F U M R B H C P N =>
      change
        some
          (CompactContinuousImageTotalBoundedUp.mk
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist X))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist F))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist U))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist M))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist R))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist B))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist H))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist C))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist P))
            (compactContinuousImageTotalBoundedDecodeBHist
              (compactContinuousImageTotalBoundedEncodeBHist N))) =
          some (CompactContinuousImageTotalBoundedUp.mk X F U M R B H C P N)
      rw [CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode X,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode F,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode U,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode M,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode R,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode B,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode H,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode C,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode P,
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode N]

private theorem
    CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactContinuousImageTotalBoundedUp} :
    compactContinuousImageTotalBoundedToEventFlow x =
        compactContinuousImageTotalBoundedToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactContinuousImageTotalBoundedFromEventFlow
          (compactContinuousImageTotalBoundedToEventFlow x) =
        compactContinuousImageTotalBoundedFromEventFlow
          (compactContinuousImageTotalBoundedToEventFlow y) :=
    congrArg compactContinuousImageTotalBoundedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_round_trip y)))

private def compactContinuousImageTotalBoundedFields :
    CompactContinuousImageTotalBoundedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactContinuousImageTotalBoundedUp.mk X F U M R B H C P N =>
      [X, F, U, M, R, B, H, C, P, N]

private theorem CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactContinuousImageTotalBoundedUp,
      compactContinuousImageTotalBoundedFields x = compactContinuousImageTotalBoundedFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 F1 U1 M1 R1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 U2 M2 R2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactContinuousImageTotalBoundedBHistCarrier :
    BHistCarrier CompactContinuousImageTotalBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactContinuousImageTotalBoundedToEventFlow
  fromEventFlow := compactContinuousImageTotalBoundedFromEventFlow

instance compactContinuousImageTotalBoundedChapterTasteGate :
    ChapterTasteGate CompactContinuousImageTotalBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactContinuousImageTotalBoundedFromEventFlow
          (compactContinuousImageTotalBoundedToEventFlow x) =
        some x
    exact CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance compactContinuousImageTotalBoundedFieldFaithful :
    FieldFaithful CompactContinuousImageTotalBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactContinuousImageTotalBoundedFields
  field_faithful := CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_fields

instance compactContinuousImageTotalBoundedNontrivial :
    Nontrivial CompactContinuousImageTotalBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactContinuousImageTotalBoundedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactContinuousImageTotalBoundedUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactContinuousImageTotalBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactContinuousImageTotalBoundedChapterTasteGate

theorem CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactContinuousImageTotalBoundedDecodeBHist
          (compactContinuousImageTotalBoundedEncodeBHist h) =
        h) ∧
      (∀ x : CompactContinuousImageTotalBoundedUp,
        compactContinuousImageTotalBoundedFromEventFlow
            (compactContinuousImageTotalBoundedToEventFlow x) =
          some x) ∧
        (∀ x y : CompactContinuousImageTotalBoundedUp,
          compactContinuousImageTotalBoundedToEventFlow x =
              compactContinuousImageTotalBoundedToEventFlow y →
            x = y) ∧
          compactContinuousImageTotalBoundedEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_decode,
      CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CompactContinuousImageTotalBoundedTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.CompactContinuousImageTotalBoundedUp
