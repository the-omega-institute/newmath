import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedLimitUp : Type where
  | mk (S D R L E H C P N : BHist) : BishopLocatedLimitUp
  deriving DecidableEq

def bishopLocatedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedLimitEncodeBHist h

def bishopLocatedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedLimitDecodeBHist tail)

private theorem BishopLocatedLimitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopLocatedLimitFields : BishopLocatedLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedLimitUp.mk S D R L E H C P N => [S, D, R, L, E, H, C, P, N]

def bishopLocatedLimitToEventFlow : BishopLocatedLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopLocatedLimitFields x).map bishopLocatedLimitEncodeBHist

private def bishopLocatedLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedLimitEventAtDefault index rest

def bishopLocatedLimitFromEventFlow (ef : EventFlow) : Option BishopLocatedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedLimitUp.mk
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 0 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 1 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 2 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 3 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 4 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 5 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 6 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 7 ef))
      (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEventAtDefault 8 ef)))

private theorem BishopLocatedLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedLimitUp,
      bishopLocatedLimitFromEventFlow (bishopLocatedLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D R L E H C P N =>
      change
        some
          (BishopLocatedLimitUp.mk
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist S))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist D))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist R))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist L))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist E))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist H))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist C))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist P))
            (bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist N))) =
          some (BishopLocatedLimitUp.mk S D R L E H C P N)
      rw [BishopLocatedLimitTasteGate_single_carrier_alignment_decode S,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode D,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode R,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode L,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode E,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode H,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode C,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode P,
        BishopLocatedLimitTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedLimitUp} :
    bishopLocatedLimitToEventFlow x = bishopLocatedLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedLimitFromEventFlow (bishopLocatedLimitToEventFlow x) =
        bishopLocatedLimitFromEventFlow (bishopLocatedLimitToEventFlow y) :=
    congrArg bishopLocatedLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopLocatedLimitTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedLimitTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopLocatedLimitUp,
      bishopLocatedLimitFields x = bishopLocatedLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 D1 R1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 D2 R2 L2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedLimitBHistCarrier : BHistCarrier BishopLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedLimitToEventFlow
  fromEventFlow := bishopLocatedLimitFromEventFlow

instance bishopLocatedLimitChapterTasteGate : ChapterTasteGate BishopLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedLimitFromEventFlow (bishopLocatedLimitToEventFlow x) = some x
    exact BishopLocatedLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopLocatedLimitFieldFaithful : FieldFaithful BishopLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedLimitFields
  field_faithful := BishopLocatedLimitTasteGate_single_carrier_alignment_fields

instance bishopLocatedLimitNontrivial : Nontrivial BishopLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedLimitChapterTasteGate

theorem BishopLocatedLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopLocatedLimitDecodeBHist (bishopLocatedLimitEncodeBHist h) = h) ∧
      bishopLocatedLimitEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : BishopLocatedLimitUp,
          bishopLocatedLimitFields x = bishopLocatedLimitFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨BishopLocatedLimitTasteGate_single_carrier_alignment_decode, rfl,
      BishopLocatedLimitTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.BishopLocatedLimitUp
