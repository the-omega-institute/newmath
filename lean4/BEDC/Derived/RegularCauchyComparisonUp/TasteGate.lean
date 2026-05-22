import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyComparisonUp : Type where
  | mk (X Y W D tau L E H C P N : BHist) : RegularCauchyComparisonUp
  deriving DecidableEq

def regularCauchyComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyComparisonEncodeBHist h

def regularCauchyComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyComparisonDecodeBHist tail)

private theorem RegularCauchyComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularCauchyComparisonDecodeBHist
      (regularCauchyComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyComparisonFields : RegularCauchyComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyComparisonUp.mk X Y W D tau L E H C P N => [X, Y, W, D, tau, L, E, H, C, P, N]

def regularCauchyComparisonToEventFlow : RegularCauchyComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyComparisonFields x).map regularCauchyComparisonEncodeBHist

def regularCauchyComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyComparisonEventAtDefault index rest

def regularCauchyComparisonFromEventFlow (ef : EventFlow) :
    Option RegularCauchyComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyComparisonUp.mk
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 0 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 1 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 2 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 3 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 4 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 5 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 6 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 7 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 8 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 9 ef))
      (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEventAtDefault 10 ef)))

private theorem RegularCauchyComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyComparisonUp,
      regularCauchyComparisonFromEventFlow (regularCauchyComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y W D tau L E H C P N =>
      change
        some
          (RegularCauchyComparisonUp.mk
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist X))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist Y))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist W))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist D))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist tau))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist L))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist E))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist H))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist C))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist P))
            (regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist N))) =
          some (RegularCauchyComparisonUp.mk X Y W D tau L E H C P N)
      rw [RegularCauchyComparisonTasteGate_single_carrier_alignment_decode X,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode Y,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode W,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode D,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode tau,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode L,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode E,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode H,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode C,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode P,
        RegularCauchyComparisonTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyComparisonUp} :
    regularCauchyComparisonToEventFlow x = regularCauchyComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyComparisonFromEventFlow (regularCauchyComparisonToEventFlow x) =
        regularCauchyComparisonFromEventFlow (regularCauchyComparisonToEventFlow y) :=
    congrArg regularCauchyComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyComparisonTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyComparisonTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyComparisonUp, regularCauchyComparisonFields x =
      regularCauchyComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 W1 D1 tau1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 W2 D2 tau2 L2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyComparisonBHistCarrier : BHistCarrier RegularCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyComparisonToEventFlow
  fromEventFlow := regularCauchyComparisonFromEventFlow

instance regularCauchyComparisonChapterTasteGate :
    ChapterTasteGate RegularCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyComparisonFromEventFlow (regularCauchyComparisonToEventFlow x) =
      some x
    exact RegularCauchyComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyComparisonFieldFaithful : FieldFaithful RegularCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyComparisonFields
  field_faithful := RegularCauchyComparisonTasteGate_single_carrier_alignment_fields

instance regularCauchyComparisonNontrivial : Nontrivial RegularCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyComparisonChapterTasteGate

theorem RegularCauchyComparisonTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyComparisonUp) ∧
      Nonempty (FieldFaithful RegularCauchyComparisonUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyComparisonUp) ∧
          (∀ h : BHist,
            regularCauchyComparisonDecodeBHist (regularCauchyComparisonEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyComparisonUp,
              regularCauchyComparisonFromEventFlow (regularCauchyComparisonToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyComparisonUp,
                regularCauchyComparisonToEventFlow x =
                  regularCauchyComparisonToEventFlow y → x = y) ∧
                regularCauchyComparisonEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyComparisonChapterTasteGate⟩,
      ⟨regularCauchyComparisonFieldFaithful⟩,
      ⟨regularCauchyComparisonNontrivial⟩,
      RegularCauchyComparisonTasteGate_single_carrier_alignment_decode,
      RegularCauchyComparisonTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyComparisonUp
