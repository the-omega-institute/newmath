import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubshiftOfFiniteTypeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubshiftOfFiniteTypeUp : Type where
  | mk (A W F L P N : BHist) : SubshiftOfFiniteTypeUp
  deriving DecidableEq

def subshiftOfFiniteTypeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subshiftOfFiniteTypeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subshiftOfFiniteTypeEncodeBHist h

def subshiftOfFiniteTypeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subshiftOfFiniteTypeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subshiftOfFiniteTypeDecodeBHist tail)

private theorem SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      subshiftOfFiniteTypeDecodeBHist
        (subshiftOfFiniteTypeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subshiftOfFiniteTypeFields : SubshiftOfFiniteTypeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubshiftOfFiniteTypeUp.mk A W F L P N => [A, W, F, L, P, N]

def subshiftOfFiniteTypeToEventFlow : SubshiftOfFiniteTypeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map subshiftOfFiniteTypeEncodeBHist (subshiftOfFiniteTypeFields x)

def subshiftOfFiniteTypeFromEventFlow
    (ef : EventFlow) : Option SubshiftOfFiniteTypeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [A, W, F, L, P, N] =>
      some
        (SubshiftOfFiniteTypeUp.mk
          (subshiftOfFiniteTypeDecodeBHist A)
          (subshiftOfFiniteTypeDecodeBHist W)
          (subshiftOfFiniteTypeDecodeBHist F)
          (subshiftOfFiniteTypeDecodeBHist L)
          (subshiftOfFiniteTypeDecodeBHist P)
          (subshiftOfFiniteTypeDecodeBHist N))
  | _ => none

private theorem SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SubshiftOfFiniteTypeUp,
      subshiftOfFiniteTypeFromEventFlow
        (subshiftOfFiniteTypeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W F L P N =>
      change
        some
          (SubshiftOfFiniteTypeUp.mk
            (subshiftOfFiniteTypeDecodeBHist
              (subshiftOfFiniteTypeEncodeBHist A))
            (subshiftOfFiniteTypeDecodeBHist
              (subshiftOfFiniteTypeEncodeBHist W))
            (subshiftOfFiniteTypeDecodeBHist
              (subshiftOfFiniteTypeEncodeBHist F))
            (subshiftOfFiniteTypeDecodeBHist
              (subshiftOfFiniteTypeEncodeBHist L))
            (subshiftOfFiniteTypeDecodeBHist
              (subshiftOfFiniteTypeEncodeBHist P))
            (subshiftOfFiniteTypeDecodeBHist
              (subshiftOfFiniteTypeEncodeBHist N))) =
          some (SubshiftOfFiniteTypeUp.mk A W F L P N)
      rw [SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode A,
        SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode W,
        SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode F,
        SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode L,
        SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode P,
        SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode N]

private theorem SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_injective
    {x y : SubshiftOfFiniteTypeUp} :
    subshiftOfFiniteTypeToEventFlow x =
      subshiftOfFiniteTypeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subshiftOfFiniteTypeFromEventFlow
          (subshiftOfFiniteTypeToEventFlow x) =
        subshiftOfFiniteTypeFromEventFlow
          (subshiftOfFiniteTypeToEventFlow y) :=
    congrArg subshiftOfFiniteTypeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_round_trip y)))

private theorem SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_fields :
    ∀ x y : SubshiftOfFiniteTypeUp,
      subshiftOfFiniteTypeFields x = subshiftOfFiniteTypeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 W1 F1 L1 P1 N1 =>
      cases y with
      | mk A2 W2 F2 L2 P2 N2 =>
          cases hfields
          rfl

instance subshiftOfFiniteTypeBHistCarrier :
    BHistCarrier SubshiftOfFiniteTypeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subshiftOfFiniteTypeToEventFlow
  fromEventFlow := subshiftOfFiniteTypeFromEventFlow

instance subshiftOfFiniteTypeChapterTasteGate :
    ChapterTasteGate SubshiftOfFiniteTypeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subshiftOfFiniteTypeFromEventFlow
        (subshiftOfFiniteTypeToEventFlow x) = some x
    exact SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SubshiftOfFiniteTypeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subshiftOfFiniteTypeChapterTasteGate

instance subshiftOfFiniteTypeFieldFaithful :
    FieldFaithful SubshiftOfFiniteTypeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := subshiftOfFiniteTypeFields
  field_faithful := SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_fields

instance subshiftOfFiniteTypeNontrivial :
    Nontrivial SubshiftOfFiniteTypeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubshiftOfFiniteTypeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SubshiftOfFiniteTypeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SubshiftOfFiniteTypeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      subshiftOfFiniteTypeDecodeBHist
        (subshiftOfFiniteTypeEncodeBHist h) = h) ∧
      (∀ x : SubshiftOfFiniteTypeUp,
        subshiftOfFiniteTypeToEventFlow x =
          List.map subshiftOfFiniteTypeEncodeBHist
            (subshiftOfFiniteTypeFields x)) ∧
        (∀ x y : SubshiftOfFiniteTypeUp,
          subshiftOfFiniteTypeFields x = subshiftOfFiniteTypeFields y →
            x = y) ∧
          (∃ x y : SubshiftOfFiniteTypeUp, x ≠ y) ∧
            subshiftOfFiniteTypeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_decode,
      (fun _ => rfl),
      SubshiftOfFiniteTypeTasteGate_single_carrier_alignment_fields,
      ⟨SubshiftOfFiniteTypeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        SubshiftOfFiniteTypeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.SubshiftOfFiniteTypeUp
