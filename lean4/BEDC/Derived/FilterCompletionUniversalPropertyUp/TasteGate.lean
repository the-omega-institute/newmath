import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterCompletionUniversalPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilterCompletionUniversalPropertyUp : Type where
  | mk (C L E Q F R A H K P N : BHist) : FilterCompletionUniversalPropertyUp
  deriving DecidableEq

def filterCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filterCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filterCompletionUniversalPropertyEncodeBHist h

def filterCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filterCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filterCompletionUniversalPropertyDecodeBHist tail)

private theorem FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def filterCompletionUniversalPropertyFields :
    FilterCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterCompletionUniversalPropertyUp.mk C L E Q F R A H K P N =>
      [C, L, E, Q, F, R, A, H, K, P, N]

def filterCompletionUniversalPropertyToEventFlow :
    FilterCompletionUniversalPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (filterCompletionUniversalPropertyFields x).map
    filterCompletionUniversalPropertyEncodeBHist

private def filterCompletionUniversalPropertyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      filterCompletionUniversalPropertyEventAtDefault index rest

def filterCompletionUniversalPropertyFromEventFlow
    (ef : EventFlow) : Option FilterCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FilterCompletionUniversalPropertyUp.mk
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 0 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 1 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 2 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 3 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 4 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 5 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 6 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 7 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 8 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 9 ef))
      (filterCompletionUniversalPropertyDecodeBHist
        (filterCompletionUniversalPropertyEventAtDefault 10 ef)))

private theorem FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FilterCompletionUniversalPropertyUp,
      filterCompletionUniversalPropertyFromEventFlow
        (filterCompletionUniversalPropertyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C L E Q F R A H K P N =>
      change
        some
          (FilterCompletionUniversalPropertyUp.mk
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist C))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist L))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist E))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist Q))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist F))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist R))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist A))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist H))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist K))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist P))
            (filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist N))) =
          some (FilterCompletionUniversalPropertyUp.mk C L E Q F R A H K P N)
      rw [FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode C,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode L,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode E,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode Q,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode F,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode R,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode A,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode H,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode K,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode P,
        FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode N]

private theorem FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_injective
    {x y : FilterCompletionUniversalPropertyUp} :
    filterCompletionUniversalPropertyToEventFlow x =
      filterCompletionUniversalPropertyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filterCompletionUniversalPropertyFromEventFlow
          (filterCompletionUniversalPropertyToEventFlow x) =
        filterCompletionUniversalPropertyFromEventFlow
          (filterCompletionUniversalPropertyToEventFlow y) :=
    congrArg filterCompletionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip y)))

private theorem FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_fields :
    ∀ x y : FilterCompletionUniversalPropertyUp,
      filterCompletionUniversalPropertyFields x =
        filterCompletionUniversalPropertyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 L1 E1 Q1 F1 R1 A1 H1 K1 P1 N1 =>
      cases y with
      | mk C2 L2 E2 Q2 F2 R2 A2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance filterCompletionUniversalPropertyBHistCarrier :
    BHistCarrier FilterCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filterCompletionUniversalPropertyToEventFlow
  fromEventFlow := filterCompletionUniversalPropertyFromEventFlow

instance filterCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate FilterCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      filterCompletionUniversalPropertyFromEventFlow
        (filterCompletionUniversalPropertyToEventFlow x) = some x
    exact FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_injective heq)

instance filterCompletionUniversalPropertyFieldFaithful :
    FieldFaithful FilterCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := filterCompletionUniversalPropertyFields
  field_faithful := FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_fields

instance filterCompletionUniversalPropertyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FilterCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FilterCompletionUniversalPropertyUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FilterCompletionUniversalPropertyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FilterCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterCompletionUniversalPropertyChapterTasteGate

theorem FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FilterCompletionUniversalPropertyUp) ∧
      Nonempty (FieldFaithful FilterCompletionUniversalPropertyUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FilterCompletionUniversalPropertyUp) ∧
          (∀ h : BHist,
            filterCompletionUniversalPropertyDecodeBHist
              (filterCompletionUniversalPropertyEncodeBHist h) = h) ∧
            (∀ x : FilterCompletionUniversalPropertyUp,
              filterCompletionUniversalPropertyFromEventFlow
                (filterCompletionUniversalPropertyToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨filterCompletionUniversalPropertyChapterTasteGate⟩,
      ⟨filterCompletionUniversalPropertyFieldFaithful⟩,
      ⟨filterCompletionUniversalPropertyNontrivial⟩,
      FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode,
      FilterCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.FilterCompletionUniversalPropertyUp
