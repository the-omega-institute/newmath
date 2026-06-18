import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalCanonicalFormUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalCanonicalFormUp : Type where
  | mk (V L M S I B A H C P N : BHist) : RationalCanonicalFormUp
  deriving DecidableEq

def rationalCanonicalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalCanonicalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalCanonicalFormEncodeBHist h

def rationalCanonicalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalCanonicalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalCanonicalFormDecodeBHist tail)

private theorem RationalCanonicalFormTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalCanonicalFormFields : RationalCanonicalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalCanonicalFormUp.mk V L M S I B A H C P N =>
      [V, L, M, S, I, B, A, H, C, P, N]

def rationalCanonicalFormToEventFlow : RationalCanonicalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalCanonicalFormFields x).map rationalCanonicalFormEncodeBHist

private def rationalCanonicalFormEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalCanonicalFormEventAtDefault index rest

def rationalCanonicalFormFromEventFlow (ef : EventFlow) :
    Option RationalCanonicalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalCanonicalFormUp.mk
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 0 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 1 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 2 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 3 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 4 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 5 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 6 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 7 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 8 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 9 ef))
      (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEventAtDefault 10 ef)))

private theorem RationalCanonicalFormTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RationalCanonicalFormUp,
      rationalCanonicalFormFromEventFlow (rationalCanonicalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V L M S I B A H C P N =>
      change
        some
          (RationalCanonicalFormUp.mk
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist V))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist L))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist M))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist S))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist I))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist B))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist A))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist H))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist C))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist P))
            (rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist N))) =
          some (RationalCanonicalFormUp.mk V L M S I B A H C P N)
      rw [RationalCanonicalFormTasteGate_single_carrier_alignment_decode V,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode L,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode M,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode S,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode I,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode B,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode A,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode H,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode C,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode P,
        RationalCanonicalFormTasteGate_single_carrier_alignment_decode N]

private theorem RationalCanonicalFormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalCanonicalFormUp} :
    rationalCanonicalFormToEventFlow x = rationalCanonicalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalCanonicalFormFromEventFlow (rationalCanonicalFormToEventFlow x) =
        rationalCanonicalFormFromEventFlow (rationalCanonicalFormToEventFlow y) :=
    congrArg rationalCanonicalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RationalCanonicalFormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalCanonicalFormTasteGate_single_carrier_alignment_round_trip y)))

private theorem RationalCanonicalFormTasteGate_single_carrier_alignment_fields :
    ∀ x y : RationalCanonicalFormUp,
      rationalCanonicalFormFields x = rationalCanonicalFormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance rationalCanonicalFormBHistCarrier : BHistCarrier RationalCanonicalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalCanonicalFormToEventFlow
  fromEventFlow := rationalCanonicalFormFromEventFlow

instance rationalCanonicalFormChapterTasteGate :
    ChapterTasteGate RationalCanonicalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalCanonicalFormFromEventFlow (rationalCanonicalFormToEventFlow x) = some x
    exact RationalCanonicalFormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RationalCanonicalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rationalCanonicalFormFieldFaithful :
    FieldFaithful RationalCanonicalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalCanonicalFormFields
  field_faithful := RationalCanonicalFormTasteGate_single_carrier_alignment_fields

instance rationalCanonicalFormNontrivial :
    Nontrivial RationalCanonicalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalCanonicalFormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RationalCanonicalFormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RationalCanonicalFormTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RationalCanonicalFormUp) ∧
      Nonempty (FieldFaithful RationalCanonicalFormUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RationalCanonicalFormUp) ∧
      (∀ h : BHist,
        rationalCanonicalFormDecodeBHist (rationalCanonicalFormEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨rationalCanonicalFormChapterTasteGate⟩,
      ⟨rationalCanonicalFormFieldFaithful⟩,
      ⟨rationalCanonicalFormNontrivial⟩,
      RationalCanonicalFormTasteGate_single_carrier_alignment_decode⟩

end BEDC.Derived.RationalCanonicalFormUp.TasteGate
