import BEDC.Derived.RegularCauchyTailAgreementUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailAgreementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailAgreementUp : Type where
  | mk (X Y S D A R H C P N : BHist) : RegularCauchyTailAgreementUp
  deriving DecidableEq

def regularCauchyTailAgreementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailAgreementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailAgreementEncodeBHist h

def regularCauchyTailAgreementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailAgreementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailAgreementDecodeBHist tail)

private theorem RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyTailAgreementDecodeBHist
        (regularCauchyTailAgreementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailAgreementFields : RegularCauchyTailAgreementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailAgreementUp.mk X Y S D A R H C P N => [X, Y, S, D, A, R, H, C, P, N]

def regularCauchyTailAgreementToEventFlow : RegularCauchyTailAgreementUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun token => (regularCauchyTailAgreementFields token).map regularCauchyTailAgreementEncodeBHist

private def regularCauchyTailAgreementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailAgreementEventAtDefault index rest

def regularCauchyTailAgreementFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTailAgreementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailAgreementUp.mk
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 0 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 1 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 2 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 3 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 4 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 5 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 6 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 7 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 8 ef))
      (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEventAtDefault 9 ef)))

private theorem RegularCauchyTailAgreementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyTailAgreementUp,
      regularCauchyTailAgreementFromEventFlow
          (regularCauchyTailAgreementToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y S D A R H C P N =>
      change
        some
          (RegularCauchyTailAgreementUp.mk
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist X))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist Y))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist S))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist D))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist A))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist R))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist H))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist C))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist P))
            (regularCauchyTailAgreementDecodeBHist (regularCauchyTailAgreementEncodeBHist N))) =
          some (RegularCauchyTailAgreementUp.mk X Y S D A R H C P N)
      rw [RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode X,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode Y,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode S,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode D,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode A,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode R,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode H,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode C,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode P,
        RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyTailAgreementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTailAgreementUp} :
    regularCauchyTailAgreementToEventFlow x = regularCauchyTailAgreementToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailAgreementFromEventFlow
          (regularCauchyTailAgreementToEventFlow x) =
        regularCauchyTailAgreementFromEventFlow
          (regularCauchyTailAgreementToEventFlow y) :=
    congrArg regularCauchyTailAgreementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTailAgreementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTailAgreementTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyTailAgreementTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyTailAgreementUp,
      regularCauchyTailAgreementFields x = regularCauchyTailAgreementFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 S1 D1 A1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 S2 D2 A2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyTailAgreementBHistCarrier :
    BHistCarrier RegularCauchyTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailAgreementToEventFlow
  fromEventFlow := regularCauchyTailAgreementFromEventFlow

instance regularCauchyTailAgreementChapterTasteGate :
    ChapterTasteGate RegularCauchyTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailAgreementFromEventFlow
          (regularCauchyTailAgreementToEventFlow x) =
        some x
    exact RegularCauchyTailAgreementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTailAgreementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyTailAgreementFieldFaithful :
    FieldFaithful RegularCauchyTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailAgreementFields
  field_faithful := RegularCauchyTailAgreementTasteGate_single_carrier_alignment_fields

instance regularCauchyTailAgreementNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailAgreementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailAgreementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailAgreementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailAgreementChapterTasteGate

theorem RegularCauchyTailAgreementTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyTailAgreementUp) ∧
      (∀ h : BHist,
        regularCauchyTailAgreementDecodeBHist
          (regularCauchyTailAgreementEncodeBHist h) = h) ∧
      regularCauchyTailAgreementEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyTailAgreementChapterTasteGate⟩,
      RegularCauchyTailAgreementTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.RegularCauchyTailAgreementUp
