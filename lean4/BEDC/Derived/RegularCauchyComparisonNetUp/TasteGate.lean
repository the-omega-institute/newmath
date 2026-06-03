import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyComparisonNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyComparisonNetUp : Type where
  | mk (M W D Q E H C P N : BHist) : RegularCauchyComparisonNetUp
  deriving DecidableEq

def regularCauchyComparisonNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyComparisonNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyComparisonNetEncodeBHist h

def regularCauchyComparisonNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyComparisonNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyComparisonNetDecodeBHist tail)

private theorem RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def regularCauchyComparisonNetFields :
    RegularCauchyComparisonNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyComparisonNetUp.mk M W D Q E H C P N => [M, W, D, Q, E, H, C, P, N]

def regularCauchyComparisonNetToEventFlow :
    RegularCauchyComparisonNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (regularCauchyComparisonNetFields token).map regularCauchyComparisonNetEncodeBHist

private def regularCauchyComparisonNetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyComparisonNetEventAtDefault index rest

def regularCauchyComparisonNetFromEventFlow
    (ef : EventFlow) : Option RegularCauchyComparisonNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyComparisonNetUp.mk
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 0 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 1 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 2 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 3 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 4 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 5 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 6 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 7 ef))
      (regularCauchyComparisonNetDecodeBHist
        (regularCauchyComparisonNetEventAtDefault 8 ef)))

private theorem RegularCauchyComparisonNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyComparisonNetUp,
      regularCauchyComparisonNetFromEventFlow
        (regularCauchyComparisonNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M W D Q E H C P N =>
      change
        some
          (RegularCauchyComparisonNetUp.mk
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist M))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist W))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist D))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist Q))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist E))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist H))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist C))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist P))
            (regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist N))) =
          some (RegularCauchyComparisonNetUp.mk M W D Q E H C P N)
      rw [RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode M,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode W,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode D,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode E,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode H,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode C,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode P,
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyComparisonNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyComparisonNetUp} :
    regularCauchyComparisonNetToEventFlow x =
        regularCauchyComparisonNetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyComparisonNetFromEventFlow
          (regularCauchyComparisonNetToEventFlow x) =
        regularCauchyComparisonNetFromEventFlow
          (regularCauchyComparisonNetToEventFlow y) :=
    congrArg regularCauchyComparisonNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyComparisonNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyComparisonNetTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyComparisonNetTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyComparisonNetUp,
      regularCauchyComparisonNetFields x = regularCauchyComparisonNetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 W1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 W2 D2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyComparisonNetBHistCarrier :
    BHistCarrier RegularCauchyComparisonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyComparisonNetToEventFlow
  fromEventFlow := regularCauchyComparisonNetFromEventFlow

instance regularCauchyComparisonNetChapterTasteGate :
    ChapterTasteGate RegularCauchyComparisonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyComparisonNetFromEventFlow
        (regularCauchyComparisonNetToEventFlow x) = some x
    exact RegularCauchyComparisonNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyComparisonNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyComparisonNetFieldFaithful :
    FieldFaithful RegularCauchyComparisonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyComparisonNetFields
  field_faithful := RegularCauchyComparisonNetTasteGate_single_carrier_alignment_fields

instance regularCauchyComparisonNetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyComparisonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyComparisonNetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyComparisonNetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyComparisonNetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyComparisonNetUp) ∧
      Nonempty (FieldFaithful RegularCauchyComparisonNetUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyComparisonNetUp) ∧
          (∀ h : BHist,
            regularCauchyComparisonNetDecodeBHist
              (regularCauchyComparisonNetEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyComparisonNetUp,
              regularCauchyComparisonNetFromEventFlow
                (regularCauchyComparisonNetToEventFlow x) = some x) ∧
              (∀ x y : RegularCauchyComparisonNetUp,
                regularCauchyComparisonNetToEventFlow x =
                    regularCauchyComparisonNetToEventFlow y →
                  x = y) ∧
                regularCauchyComparisonNetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyComparisonNetChapterTasteGate⟩,
      ⟨regularCauchyComparisonNetFieldFaithful⟩,
      ⟨regularCauchyComparisonNetNontrivial⟩,
      RegularCauchyComparisonNetTasteGate_single_carrier_alignment_decode,
      RegularCauchyComparisonNetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyComparisonNetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyComparisonNetUp
