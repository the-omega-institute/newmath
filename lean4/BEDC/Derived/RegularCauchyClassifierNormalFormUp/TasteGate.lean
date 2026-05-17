import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyClassifierNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyClassifierNormalFormUp : Type where
  | mk (D W Q R E H C P N : BHist) : RegularCauchyClassifierNormalFormUp
  deriving DecidableEq

def regularCauchyClassifierNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyClassifierNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyClassifierNormalFormEncodeBHist h

def regularCauchyClassifierNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyClassifierNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyClassifierNormalFormDecodeBHist tail)

private theorem regularCauchyClassifierNormalForm_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyClassifierNormalFormToEventFlow :
    RegularCauchyClassifierNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyClassifierNormalFormUp.mk D W Q R E H C P N =>
      [regularCauchyClassifierNormalFormEncodeBHist D,
        regularCauchyClassifierNormalFormEncodeBHist W,
        regularCauchyClassifierNormalFormEncodeBHist Q,
        regularCauchyClassifierNormalFormEncodeBHist R,
        regularCauchyClassifierNormalFormEncodeBHist E,
        regularCauchyClassifierNormalFormEncodeBHist H,
        regularCauchyClassifierNormalFormEncodeBHist C,
        regularCauchyClassifierNormalFormEncodeBHist P,
        regularCauchyClassifierNormalFormEncodeBHist N]

private def regularCauchyClassifierNormalFormEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyClassifierNormalFormEventAtDefault index rest

def regularCauchyClassifierNormalFormFromEventFlow
    (ef : EventFlow) : Option RegularCauchyClassifierNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyClassifierNormalFormUp.mk
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 0 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 1 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 2 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 3 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 4 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 5 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 6 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 7 ef))
      (regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEventAtDefault 8 ef)))

private theorem regularCauchyClassifierNormalForm_round_trip :
    ∀ x : RegularCauchyClassifierNormalFormUp,
      regularCauchyClassifierNormalFormFromEventFlow
        (regularCauchyClassifierNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q R E H C P N =>
      change
        some
          (RegularCauchyClassifierNormalFormUp.mk
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist D))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist W))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist Q))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist R))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist E))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist H))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist C))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist P))
            (regularCauchyClassifierNormalFormDecodeBHist
              (regularCauchyClassifierNormalFormEncodeBHist N))) =
          some (RegularCauchyClassifierNormalFormUp.mk D W Q R E H C P N)
      rw [regularCauchyClassifierNormalForm_decode_encode_bhist D,
        regularCauchyClassifierNormalForm_decode_encode_bhist W,
        regularCauchyClassifierNormalForm_decode_encode_bhist Q,
        regularCauchyClassifierNormalForm_decode_encode_bhist R,
        regularCauchyClassifierNormalForm_decode_encode_bhist E,
        regularCauchyClassifierNormalForm_decode_encode_bhist H,
        regularCauchyClassifierNormalForm_decode_encode_bhist C,
        regularCauchyClassifierNormalForm_decode_encode_bhist P,
        regularCauchyClassifierNormalForm_decode_encode_bhist N]

private theorem regularCauchyClassifierNormalFormToEventFlow_injective
    {x y : RegularCauchyClassifierNormalFormUp} :
    regularCauchyClassifierNormalFormToEventFlow x =
      regularCauchyClassifierNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyClassifierNormalFormFromEventFlow
          (regularCauchyClassifierNormalFormToEventFlow x) =
        regularCauchyClassifierNormalFormFromEventFlow
          (regularCauchyClassifierNormalFormToEventFlow y) :=
    congrArg regularCauchyClassifierNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyClassifierNormalForm_round_trip x).symm
      (Eq.trans hread (regularCauchyClassifierNormalForm_round_trip y)))

private def regularCauchyClassifierNormalFormFields :
    RegularCauchyClassifierNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyClassifierNormalFormUp.mk D W Q R E H C P N => [D, W, Q, R, E, H, C, P, N]

private theorem regularCauchyClassifierNormalForm_field_faithful :
    ∀ x y : RegularCauchyClassifierNormalFormUp,
      regularCauchyClassifierNormalFormFields x =
        regularCauchyClassifierNormalFormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 W1 Q1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 W2 Q2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyClassifierNormalFormBHistCarrier :
    BHistCarrier RegularCauchyClassifierNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyClassifierNormalFormToEventFlow
  fromEventFlow := regularCauchyClassifierNormalFormFromEventFlow

instance regularCauchyClassifierNormalFormChapterTasteGate :
    ChapterTasteGate RegularCauchyClassifierNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyClassifierNormalFormFromEventFlow
        (regularCauchyClassifierNormalFormToEventFlow x) = some x
    exact regularCauchyClassifierNormalForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyClassifierNormalFormToEventFlow_injective heq)

instance regularCauchyClassifierNormalFormFieldFaithful :
    FieldFaithful RegularCauchyClassifierNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyClassifierNormalFormFields
  field_faithful := regularCauchyClassifierNormalForm_field_faithful

instance regularCauchyClassifierNormalFormNontrivial :
    Nontrivial RegularCauchyClassifierNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyClassifierNormalFormUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyClassifierNormalFormUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyClassifierNormalFormTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyClassifierNormalFormDecodeBHist
        (regularCauchyClassifierNormalFormEncodeBHist h) = h) ∧
      (forall x : RegularCauchyClassifierNormalFormUp,
        regularCauchyClassifierNormalFormFromEventFlow
          (regularCauchyClassifierNormalFormToEventFlow x) = some x) ∧
        (forall x y : RegularCauchyClassifierNormalFormUp,
          regularCauchyClassifierNormalFormToEventFlow x =
            regularCauchyClassifierNormalFormToEventFlow y -> x = y) ∧
          regularCauchyClassifierNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨regularCauchyClassifierNormalForm_decode_encode_bhist,
      regularCauchyClassifierNormalForm_round_trip,
      (fun _ _ heq => regularCauchyClassifierNormalFormToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyClassifierNormalFormUp
