import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyApartnessOrderUp : Type where
  | mk (X A O M W D R E H C P N : BHist) : RegularCauchyApartnessOrderUp
  deriving DecidableEq

def regularCauchyApartnessOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyApartnessOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyApartnessOrderEncodeBHist h

def regularCauchyApartnessOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyApartnessOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyApartnessOrderDecodeBHist tail)

private theorem RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def regularCauchyApartnessOrderFields :
    RegularCauchyApartnessOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyApartnessOrderUp.mk X A O M W D R E H C P N =>
      [X, A, O, M, W, D, R, E, H, C, P, N]

def regularCauchyApartnessOrderToEventFlow :
    RegularCauchyApartnessOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (regularCauchyApartnessOrderFields token).map regularCauchyApartnessOrderEncodeBHist

private def regularCauchyApartnessOrderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyApartnessOrderEventAtDefault index rest

def regularCauchyApartnessOrderFromEventFlow
    (ef : EventFlow) : Option RegularCauchyApartnessOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyApartnessOrderUp.mk
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 0 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 1 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 2 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 3 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 4 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 5 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 6 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 7 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 8 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 9 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 10 ef))
      (regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEventAtDefault 11 ef)))

private theorem RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyApartnessOrderUp,
      regularCauchyApartnessOrderFromEventFlow
        (regularCauchyApartnessOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X A O M W D R E H C P N =>
      change
        some
          (RegularCauchyApartnessOrderUp.mk
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist X))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist A))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist O))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist M))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist W))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist D))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist R))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist E))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist H))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist C))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist P))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist N))) =
          some (RegularCauchyApartnessOrderUp.mk X A O M W D R E H C P N)
      rw [RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode X,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode A,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode O,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode M,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode W,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode D,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode R,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode E,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode H,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode C,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode P,
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyApartnessOrderUp} :
    regularCauchyApartnessOrderToEventFlow x =
      regularCauchyApartnessOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyApartnessOrderFromEventFlow
          (regularCauchyApartnessOrderToEventFlow x) =
        regularCauchyApartnessOrderFromEventFlow
          (regularCauchyApartnessOrderToEventFlow y) :=
    congrArg regularCauchyApartnessOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyApartnessOrderUp,
      regularCauchyApartnessOrderFields x = regularCauchyApartnessOrderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 A1 O1 M1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 O2 M2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyApartnessOrderBHistCarrier :
    BHistCarrier RegularCauchyApartnessOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyApartnessOrderToEventFlow
  fromEventFlow := regularCauchyApartnessOrderFromEventFlow

instance regularCauchyApartnessOrderChapterTasteGate :
    ChapterTasteGate RegularCauchyApartnessOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyApartnessOrderFromEventFlow
        (regularCauchyApartnessOrderToEventFlow x) = some x
    exact RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyApartnessOrderFieldFaithful :
    FieldFaithful RegularCauchyApartnessOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyApartnessOrderFields
  field_faithful := RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_fields

instance regularCauchyApartnessOrderNontrivial :
    Nontrivial RegularCauchyApartnessOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyApartnessOrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyApartnessOrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyApartnessOrderUp) ∧ Nonempty (FieldFaithful RegularCauchyApartnessOrderUp) ∧ Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyApartnessOrderUp) ∧ (∀ h : BHist, regularCauchyApartnessOrderDecodeBHist (regularCauchyApartnessOrderEncodeBHist h) = h) ∧ (∀ x : RegularCauchyApartnessOrderUp, regularCauchyApartnessOrderFromEventFlow (regularCauchyApartnessOrderToEventFlow x) = some x) ∧ (∀ x y : RegularCauchyApartnessOrderUp, regularCauchyApartnessOrderToEventFlow x = regularCauchyApartnessOrderToEventFlow y → x = y) ∧ regularCauchyApartnessOrderEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyApartnessOrderChapterTasteGate⟩,
      ⟨regularCauchyApartnessOrderFieldFaithful⟩,
      ⟨regularCauchyApartnessOrderNontrivial⟩,
      RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_decode,
      RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyApartnessOrderUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyApartnessOrderUp
