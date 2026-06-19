import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNameNormalFormUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyNameNormalFormUp : Type where
  | mk (D S R M E B H C P N : BHist) : RegularCauchyNameNormalFormUp
  deriving DecidableEq

def regularCauchyNameNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyNameNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyNameNormalFormEncodeBHist h

def regularCauchyNameNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyNameNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyNameNormalFormDecodeBHist tail)

private theorem regularCauchyNameNormalFormDecode_encode :
    ∀ h : BHist,
      regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyNameNormalFormFields :
    RegularCauchyNameNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNameNormalFormUp.mk D S R M E B H C P N =>
      [D, S, R, M, E, B, H, C, P, N]

def regularCauchyNameNormalFormToEventFlow :
    RegularCauchyNameNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyNameNormalFormFields x).map regularCauchyNameNormalFormEncodeBHist

private def regularCauchyNameNormalFormEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyNameNormalFormEventAtDefault index rest

def regularCauchyNameNormalFormFromEventFlow
    (ef : EventFlow) : Option RegularCauchyNameNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyNameNormalFormUp.mk
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 0 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 1 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 2 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 3 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 4 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 5 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 6 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 7 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 8 ef))
      (regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEventAtDefault 9 ef)))

private theorem regularCauchyNameNormalForm_round_trip :
    ∀ x : RegularCauchyNameNormalFormUp,
      regularCauchyNameNormalFormFromEventFlow
        (regularCauchyNameNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R M E B H C P N =>
      change
        some
          (RegularCauchyNameNormalFormUp.mk
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist D))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist S))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist R))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist M))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist E))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist B))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist H))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist C))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist P))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist N))) =
          some (RegularCauchyNameNormalFormUp.mk D S R M E B H C P N)
      rw [regularCauchyNameNormalFormDecode_encode D,
        regularCauchyNameNormalFormDecode_encode S,
        regularCauchyNameNormalFormDecode_encode R,
        regularCauchyNameNormalFormDecode_encode M,
        regularCauchyNameNormalFormDecode_encode E,
        regularCauchyNameNormalFormDecode_encode B,
        regularCauchyNameNormalFormDecode_encode H,
        regularCauchyNameNormalFormDecode_encode C,
        regularCauchyNameNormalFormDecode_encode P,
        regularCauchyNameNormalFormDecode_encode N]

private theorem regularCauchyNameNormalFormToEventFlow_injective
    {x y : RegularCauchyNameNormalFormUp} :
    regularCauchyNameNormalFormToEventFlow x =
      regularCauchyNameNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyNameNormalFormFromEventFlow
          (regularCauchyNameNormalFormToEventFlow x) =
        regularCauchyNameNormalFormFromEventFlow
          (regularCauchyNameNormalFormToEventFlow y) :=
    congrArg regularCauchyNameNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyNameNormalForm_round_trip x).symm
      (Eq.trans hread (regularCauchyNameNormalForm_round_trip y)))

instance regularCauchyNameNormalFormBHistCarrier :
    BHistCarrier RegularCauchyNameNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNameNormalFormToEventFlow
  fromEventFlow := regularCauchyNameNormalFormFromEventFlow

instance regularCauchyNameNormalFormChapterTasteGate :
    ChapterTasteGate RegularCauchyNameNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyNameNormalFormFromEventFlow
        (regularCauchyNameNormalFormToEventFlow x) = some x
    exact regularCauchyNameNormalForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyNameNormalFormToEventFlow_injective heq)

instance regularCauchyNameNormalFormFieldFaithful :
    FieldFaithful RegularCauchyNameNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyNameNormalFormFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk D S R M E B H C P N =>
        cases y with
        | mk D' S' R' M' E' B' H' C' P' N' =>
            cases hfields
            rfl

instance regularCauchyNameNormalFormNontrivial :
    Nontrivial RegularCauchyNameNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyNameNormalFormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyNameNormalFormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyNameNormalFormTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyNameNormalFormUp,
        regularCauchyNameNormalFormFromEventFlow
          (regularCauchyNameNormalFormToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyNameNormalFormUp,
          regularCauchyNameNormalFormToEventFlow x =
            regularCauchyNameNormalFormToEventFlow y → x = y) ∧
          regularCauchyNameNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyNameNormalFormDecode_encode,
      regularCauchyNameNormalForm_round_trip,
      fun _ _ heq => regularCauchyNameNormalFormToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyNameNormalFormUp.TasteGate
