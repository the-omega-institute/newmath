import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyAffineCombinationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyAffineCombinationUp : Type where
  | mk (Q X Y WX WY DQ DQbar SX SY Sigma E R Z H C P N : BHist) :
      RegularCauchyAffineCombinationUp
  deriving DecidableEq

def regularCauchyAffineCombinationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyAffineCombinationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyAffineCombinationEncodeBHist h

def regularCauchyAffineCombinationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyAffineCombinationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyAffineCombinationDecodeBHist tail)

theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyAffineCombinationDecodeBHist
          (regularCauchyAffineCombinationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyAffineCombinationToEventFlow :
    RegularCauchyAffineCombinationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyAffineCombinationUp.mk Q X Y WX WY DQ DQbar SX SY Sigma E R Z H C P N =>
      [regularCauchyAffineCombinationEncodeBHist Q,
        regularCauchyAffineCombinationEncodeBHist X,
        regularCauchyAffineCombinationEncodeBHist Y,
        regularCauchyAffineCombinationEncodeBHist WX,
        regularCauchyAffineCombinationEncodeBHist WY,
        regularCauchyAffineCombinationEncodeBHist DQ,
        regularCauchyAffineCombinationEncodeBHist DQbar,
        regularCauchyAffineCombinationEncodeBHist SX,
        regularCauchyAffineCombinationEncodeBHist SY,
        regularCauchyAffineCombinationEncodeBHist Sigma,
        regularCauchyAffineCombinationEncodeBHist E,
        regularCauchyAffineCombinationEncodeBHist R,
        regularCauchyAffineCombinationEncodeBHist Z,
        regularCauchyAffineCombinationEncodeBHist H,
        regularCauchyAffineCombinationEncodeBHist C,
        regularCauchyAffineCombinationEncodeBHist P,
        regularCauchyAffineCombinationEncodeBHist N]

def regularCauchyAffineCombinationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyAffineCombinationEventAtDefault index rest

def regularCauchyAffineCombinationFromEventFlow
    (ef : EventFlow) : Option RegularCauchyAffineCombinationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyAffineCombinationUp.mk
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 0 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 1 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 2 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 3 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 4 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 5 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 6 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 7 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 8 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 9 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 10 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 11 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 12 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 13 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 14 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 15 ef))
      (regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEventAtDefault 16 ef)))

theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyAffineCombinationUp,
      regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q X Y WX WY DQ DQbar SX SY Sigma E R Z H C P N =>
      change
        some
          (RegularCauchyAffineCombinationUp.mk
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist Q))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist X))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist Y))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist WX))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist WY))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist DQ))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist DQbar))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist SX))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist SY))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist Sigma))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist E))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist R))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist Z))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist H))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist C))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist P))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist N))) =
          some (RegularCauchyAffineCombinationUp.mk Q X Y WX WY DQ DQbar SX SY Sigma E R Z H C P N)
      rw [RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode X,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode Y,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode WX,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode WY,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode DQ,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode DQbar,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode SX,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode SY,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode Sigma,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode E,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode R,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode Z,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode H,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode C,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode P,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode N]

theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyAffineCombinationUp} :
    regularCauchyAffineCombinationToEventFlow x =
        regularCauchyAffineCombinationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow x) =
        regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow y) :=
    congrArg regularCauchyAffineCombinationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip y)))

def regularCauchyAffineCombinationFields :
    RegularCauchyAffineCombinationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyAffineCombinationUp.mk Q X Y WX WY DQ DQbar SX SY Sigma E R Z H C P N =>
      [Q, X, Y, WX, WY, DQ, DQbar, SX, SY, Sigma, E, R, Z, H, C, P, N]

theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyAffineCombinationUp,
      regularCauchyAffineCombinationFields x = regularCauchyAffineCombinationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 X1 Y1 WX1 WY1 DQ1 DQbar1 SX1 SY1 Sigma1 E1 R1 Z1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 X2 Y2 WX2 WY2 DQ2 DQbar2 SX2 SY2 Sigma2 E2 R2 Z2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyAffineCombinationBHistCarrier :
    BHistCarrier RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyAffineCombinationToEventFlow
  fromEventFlow := regularCauchyAffineCombinationFromEventFlow

instance regularCauchyAffineCombinationChapterTasteGate :
    ChapterTasteGate RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow x) =
        some x
    exact RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyAffineCombinationFieldFaithful :
    FieldFaithful RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyAffineCombinationFields
  field_faithful := RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_fields

instance regularCauchyAffineCombinationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyAffineCombinationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyAffineCombinationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyAffineCombinationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyAffineCombinationChapterTasteGate

theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyAffineCombinationUp) ∧
      Nonempty (FieldFaithful RegularCauchyAffineCombinationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyAffineCombinationUp) ∧
          (∀ h : BHist,
            regularCauchyAffineCombinationDecodeBHist
                (regularCauchyAffineCombinationEncodeBHist h) =
              h) ∧
            (∀ x : RegularCauchyAffineCombinationUp,
              regularCauchyAffineCombinationFromEventFlow
                  (regularCauchyAffineCombinationToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyAffineCombinationUp,
                regularCauchyAffineCombinationToEventFlow x =
                    regularCauchyAffineCombinationToEventFlow y →
                  x = y) ∧
                regularCauchyAffineCombinationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyAffineCombinationChapterTasteGate⟩,
      ⟨regularCauchyAffineCombinationFieldFaithful⟩,
      ⟨regularCauchyAffineCombinationNontrivial⟩,
      RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode,
      RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyAffineCombinationUp.TasteGate
