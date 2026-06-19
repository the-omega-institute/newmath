import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AubinLionsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AubinLionsUp : Type where
  | mk (S T R M E H C P N : BHist) : AubinLionsUp
  deriving DecidableEq

def AubinLionsTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: AubinLionsTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: AubinLionsTasteGate_single_carrier_alignment_encodeBHist h

def aubinLionsEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  AubinLionsTasteGate_single_carrier_alignment_encodeBHist

def AubinLionsTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (AubinLionsTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (AubinLionsTasteGate_single_carrier_alignment_decodeBHist tail)

def aubinLionsDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  AubinLionsTasteGate_single_carrier_alignment_decodeBHist

private theorem AubinLionsTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, aubinLionsDecodeBHist (aubinLionsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def AubinLionsTasteGate_single_carrier_alignment_fields : AubinLionsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AubinLionsUp.mk S T R M E H C P N => [S, T, R, M, E, H, C, P, N]

def aubinLionsToEventFlow : AubinLionsUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (AubinLionsTasteGate_single_carrier_alignment_fields x).map aubinLionsEncodeBHist

private def AubinLionsTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AubinLionsTasteGate_single_carrier_alignment_eventAt index rest

def aubinLionsFromEventFlow : EventFlow → Option AubinLionsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AubinLionsUp.mk
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 0 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 1 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 2 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 3 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 4 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 5 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 6 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 7 ef))
        (aubinLionsDecodeBHist (AubinLionsTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem AubinLionsTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AubinLionsUp, aubinLionsFromEventFlow (aubinLionsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T R M E H C P N =>
      change
        some
          (AubinLionsUp.mk
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist S))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist T))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist R))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist M))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist E))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist H))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist C))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist P))
            (aubinLionsDecodeBHist (aubinLionsEncodeBHist N))) =
          some (AubinLionsUp.mk S T R M E H C P N)
      rw [AubinLionsTasteGate_single_carrier_alignment_decode S,
        AubinLionsTasteGate_single_carrier_alignment_decode T,
        AubinLionsTasteGate_single_carrier_alignment_decode R,
        AubinLionsTasteGate_single_carrier_alignment_decode M,
        AubinLionsTasteGate_single_carrier_alignment_decode E,
        AubinLionsTasteGate_single_carrier_alignment_decode H,
        AubinLionsTasteGate_single_carrier_alignment_decode C,
        AubinLionsTasteGate_single_carrier_alignment_decode P,
        AubinLionsTasteGate_single_carrier_alignment_decode N]

private theorem AubinLionsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AubinLionsUp} :
    aubinLionsToEventFlow x = aubinLionsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      aubinLionsFromEventFlow (aubinLionsToEventFlow x) =
        aubinLionsFromEventFlow (aubinLionsToEventFlow y) :=
    congrArg aubinLionsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AubinLionsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AubinLionsTasteGate_single_carrier_alignment_round_trip y)))

private theorem AubinLionsTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : AubinLionsUp,
      AubinLionsTasteGate_single_carrier_alignment_fields x =
        AubinLionsTasteGate_single_carrier_alignment_fields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ T₁ R₁ M₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ R₂ M₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance aubinLionsBHistCarrier : BHistCarrier AubinLionsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := aubinLionsToEventFlow
  fromEventFlow := aubinLionsFromEventFlow

instance aubinLionsChapterTasteGate : ChapterTasteGate AubinLionsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change aubinLionsFromEventFlow (aubinLionsToEventFlow x) = some x
    exact AubinLionsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AubinLionsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance aubinLionsFieldFaithful : FieldFaithful AubinLionsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := AubinLionsTasteGate_single_carrier_alignment_fields
  field_faithful := AubinLionsTasteGate_single_carrier_alignment_field_faithful

instance aubinLionsNontrivial : Nontrivial AubinLionsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AubinLionsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AubinLionsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AubinLionsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  aubinLionsChapterTasteGate

theorem AubinLionsTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier AubinLionsUp) ∧
      Nonempty (ChapterTasteGate AubinLionsUp) ∧
        Nonempty (FieldFaithful AubinLionsUp) ∧
          (∀ h : BHist, aubinLionsDecodeBHist (aubinLionsEncodeBHist h) = h) ∧
            aubinLionsEncodeBHist BHist.Empty = ([] : List BMark) ∧
              (∃ x y : AubinLionsUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨aubinLionsBHistCarrier⟩,
      ⟨⟨aubinLionsChapterTasteGate⟩,
        ⟨⟨aubinLionsFieldFaithful⟩,
          AubinLionsTasteGate_single_carrier_alignment_decode,
          rfl,
          ⟨(aubinLionsNontrivial.witness_pair).1,
            (aubinLionsNontrivial.witness_pair).2.1,
            (aubinLionsNontrivial.witness_pair).2.2⟩⟩⟩⟩

end BEDC.Derived.AubinLionsUp
