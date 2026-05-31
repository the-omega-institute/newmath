import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteGroupRepresentationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteGroupRepresentationUp : Type where
  | finiteAction :
      BHist → BHist → BHist → BHist → BHist → BHist → BHist → BHist → BHist →
        BHist → FiniteGroupRepresentationUp
  deriving DecidableEq

def finiteGroupRepresentationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteGroupRepresentationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteGroupRepresentationEncodeBHist h

def finiteGroupRepresentationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteGroupRepresentationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteGroupRepresentationDecodeBHist tail)

private theorem finiteGroupRepresentation_decode_encode :
    ∀ h : BHist,
      finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteGroupRepresentationFields : FiniteGroupRepresentationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteGroupRepresentationUp.finiteAction G V L M A U C H P N =>
      [G, V, L, M, A, U, C, H, P, N]

def finiteGroupRepresentationToEventFlow : FiniteGroupRepresentationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteGroupRepresentationFields x).map finiteGroupRepresentationEncodeBHist

private def finiteGroupRepresentationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteGroupRepresentationEventAtDefault index rest

def finiteGroupRepresentationFromEventFlow
    (ef : EventFlow) : Option FiniteGroupRepresentationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteGroupRepresentationUp.finiteAction
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 0 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 1 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 2 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 3 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 4 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 5 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 6 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 7 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 8 ef))
      (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEventAtDefault 9 ef)))

private theorem finiteGroupRepresentation_round_trip :
    ∀ x : FiniteGroupRepresentationUp,
      finiteGroupRepresentationFromEventFlow (finiteGroupRepresentationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | finiteAction G V L M A U C H P N =>
      change
        some
          (FiniteGroupRepresentationUp.finiteAction
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist G))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist V))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist L))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist M))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist A))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist U))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist C))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist H))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist P))
            (finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist N))) =
          some (FiniteGroupRepresentationUp.finiteAction G V L M A U C H P N)
      rw [finiteGroupRepresentation_decode_encode G,
        finiteGroupRepresentation_decode_encode V,
        finiteGroupRepresentation_decode_encode L,
        finiteGroupRepresentation_decode_encode M,
        finiteGroupRepresentation_decode_encode A,
        finiteGroupRepresentation_decode_encode U,
        finiteGroupRepresentation_decode_encode C,
        finiteGroupRepresentation_decode_encode H,
        finiteGroupRepresentation_decode_encode P,
        finiteGroupRepresentation_decode_encode N]

private theorem finiteGroupRepresentationToEventFlow_injective
    {x y : FiniteGroupRepresentationUp} :
    finiteGroupRepresentationToEventFlow x = finiteGroupRepresentationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteGroupRepresentationFromEventFlow (finiteGroupRepresentationToEventFlow x) =
        finiteGroupRepresentationFromEventFlow (finiteGroupRepresentationToEventFlow y) :=
    congrArg finiteGroupRepresentationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteGroupRepresentation_round_trip x).symm
      (Eq.trans hread (finiteGroupRepresentation_round_trip y)))

private theorem finiteGroupRepresentation_field_faithful :
    ∀ x y : FiniteGroupRepresentationUp,
      finiteGroupRepresentationFields x = finiteGroupRepresentationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | finiteAction G V L M A U C H P N =>
      cases y with
      | finiteAction G' V' L' M' A' U' C' H' P' N' =>
          cases hfields
          rfl

instance finiteGroupRepresentationBHistCarrier : BHistCarrier FiniteGroupRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteGroupRepresentationToEventFlow
  fromEventFlow := finiteGroupRepresentationFromEventFlow

instance finiteGroupRepresentationChapterTasteGate :
    ChapterTasteGate FiniteGroupRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteGroupRepresentationFromEventFlow (finiteGroupRepresentationToEventFlow x) =
        some x
    exact finiteGroupRepresentation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteGroupRepresentationToEventFlow_injective heq)

instance finiteGroupRepresentationFieldFaithful :
    FieldFaithful FiniteGroupRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteGroupRepresentationFields
  field_faithful := finiteGroupRepresentation_field_faithful

instance finiteGroupRepresentationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteGroupRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteGroupRepresentationUp.finiteAction (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteGroupRepresentationUp.finiteAction (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteGroupRepresentationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteGroupRepresentationChapterTasteGate

theorem FiniteGroupRepresentationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        finiteGroupRepresentationDecodeBHist (finiteGroupRepresentationEncodeBHist h) = h) ∧
      (∀ x : FiniteGroupRepresentationUp,
        finiteGroupRepresentationFromEventFlow (finiteGroupRepresentationToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteGroupRepresentationUp,
          finiteGroupRepresentationToEventFlow x =
            finiteGroupRepresentationToEventFlow y → x = y) ∧
          finiteGroupRepresentationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨finiteGroupRepresentation_decode_encode,
      finiteGroupRepresentation_round_trip,
      fun x y heq => finiteGroupRepresentationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FiniteGroupRepresentationUp
