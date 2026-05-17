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

private theorem regularCauchyClassifierNormalFormDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyClassifierNormalFormDecodeBHist
          (regularCauchyClassifierNormalFormEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyClassifierNormalFormFields :
    RegularCauchyClassifierNormalFormUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyClassifierNormalFormUp.mk D W Q R E H C P N =>
      [D, W, Q, R, E, H, C, P, N]

def regularCauchyClassifierNormalFormToEventFlow :
    RegularCauchyClassifierNormalFormUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
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

def regularCauchyClassifierNormalFormFromEventFlow :
    EventFlow → Option RegularCauchyClassifierNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | D :: W :: Q :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyClassifierNormalFormUp.mk
          (regularCauchyClassifierNormalFormDecodeBHist D)
          (regularCauchyClassifierNormalFormDecodeBHist W)
          (regularCauchyClassifierNormalFormDecodeBHist Q)
          (regularCauchyClassifierNormalFormDecodeBHist R)
          (regularCauchyClassifierNormalFormDecodeBHist E)
          (regularCauchyClassifierNormalFormDecodeBHist H)
          (regularCauchyClassifierNormalFormDecodeBHist C)
          (regularCauchyClassifierNormalFormDecodeBHist P)
          (regularCauchyClassifierNormalFormDecodeBHist N))
  | _ => none

private theorem regularCauchyClassifierNormalForm_round_trip :
    ∀ x : RegularCauchyClassifierNormalFormUp,
      regularCauchyClassifierNormalFormFromEventFlow
          (regularCauchyClassifierNormalFormToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q R E H C P N =>
      simp only [regularCauchyClassifierNormalFormToEventFlow,
        regularCauchyClassifierNormalFormFromEventFlow,
        regularCauchyClassifierNormalFormDecode_encode_bhist]

private theorem regularCauchyClassifierNormalFormToEventFlow_injective
    {x y : RegularCauchyClassifierNormalFormUp} :
    regularCauchyClassifierNormalFormToEventFlow x =
        regularCauchyClassifierNormalFormToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyClassifierNormalFormFromEventFlow
            (regularCauchyClassifierNormalFormToEventFlow x) :=
        (regularCauchyClassifierNormalForm_round_trip x).symm
      _ =
          regularCauchyClassifierNormalFormFromEventFlow
            (regularCauchyClassifierNormalFormToEventFlow y) :=
        congrArg regularCauchyClassifierNormalFormFromEventFlow hxy
      _ = some y := regularCauchyClassifierNormalForm_round_trip y
  exact Option.some.inj optionEq

private theorem regularCauchyClassifierNormalForm_field_faithful :
    ∀ x y : RegularCauchyClassifierNormalFormUp,
      regularCauchyClassifierNormalFormFields x =
          regularCauchyClassifierNormalFormFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D1 W1 Q1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 W2 Q2 R2 E2 H2 C2 P2 N2 =>
          cases h
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
          (regularCauchyClassifierNormalFormToEventFlow x) =
        some x
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
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyClassifierNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyClassifierNormalFormUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyClassifierNormalFormUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyClassifierNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyClassifierNormalFormChapterTasteGate

end BEDC.Derived.RegularCauchyClassifierNormalFormUp
