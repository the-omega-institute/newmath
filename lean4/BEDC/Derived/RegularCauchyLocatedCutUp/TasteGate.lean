import BEDC.Derived.RegularCauchyLocatedCutUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularCauchyLocatedCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedCutEncodeBHist h

def regularCauchyLocatedCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedCutDecodeBHist tail)

private theorem RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularCauchyLocatedCutDecodeBHist
      (regularCauchyLocatedCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocatedCutToEventFlow : RegularCauchyLocatedCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map regularCauchyLocatedCutEncodeBHist (regularCauchyLocatedCutFields x)

private def regularCauchyLocatedCutEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLocatedCutEventAtDefault index rest

def regularCauchyLocatedCutFromEventFlow :
    EventFlow → Option RegularCauchyLocatedCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyLocatedCutUp.mk
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 0 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 1 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 2 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 3 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 4 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 5 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 6 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 7 ef))
        (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEventAtDefault 8 ef)))

private theorem RegularCauchyLocatedCutTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyLocatedCutUp,
      regularCauchyLocatedCutFromEventFlow (regularCauchyLocatedCutToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D L R H C P N =>
      change
        some
          (RegularCauchyLocatedCutUp.mk
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist S))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist Q))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist D))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist L))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist R))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist H))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist C))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist P))
            (regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist N))) =
          some (RegularCauchyLocatedCutUp.mk S Q D L R H C P N)
      rw [RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode S,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode D,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode L,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode R,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode H,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode C,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode P,
        RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyLocatedCutTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyLocatedCutUp,
      regularCauchyLocatedCutFields x = regularCauchyLocatedCutFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 Q1 D1 L1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 Q2 D2 L2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

private theorem RegularCauchyLocatedCutTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyLocatedCutUp} :
    regularCauchyLocatedCutToEventFlow x = regularCauchyLocatedCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedCutFromEventFlow (regularCauchyLocatedCutToEventFlow x) =
        regularCauchyLocatedCutFromEventFlow (regularCauchyLocatedCutToEventFlow y) :=
    congrArg regularCauchyLocatedCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyLocatedCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyLocatedCutTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyLocatedCutBHistCarrier : BHistCarrier RegularCauchyLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedCutToEventFlow
  fromEventFlow := regularCauchyLocatedCutFromEventFlow

instance regularCauchyLocatedCutChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedCutFromEventFlow (regularCauchyLocatedCutToEventFlow x) =
        some x
    exact RegularCauchyLocatedCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyLocatedCutTasteGate_single_carrier_alignment_injective heq)

instance regularCauchyLocatedCutFieldFaithful :
    FieldFaithful RegularCauchyLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLocatedCutFields
  field_faithful := RegularCauchyLocatedCutTasteGate_single_carrier_alignment_fields

instance regularCauchyLocatedCutNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyLocatedCutUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyLocatedCutUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyLocatedCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocatedCutChapterTasteGate

theorem RegularCauchyLocatedCutTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyLocatedCutUp) ∧
      Nonempty (FieldFaithful RegularCauchyLocatedCutUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyLocatedCutUp) ∧
      (∀ h : BHist,
        regularCauchyLocatedCutDecodeBHist (regularCauchyLocatedCutEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLocatedCutUp,
        regularCauchyLocatedCutFromEventFlow (regularCauchyLocatedCutToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyLocatedCutUp,
        regularCauchyLocatedCutToEventFlow x = regularCauchyLocatedCutToEventFlow y →
          x = y) ∧
      regularCauchyLocatedCutEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact Nonempty.intro regularCauchyLocatedCutChapterTasteGate
  · constructor
    · exact Nonempty.intro regularCauchyLocatedCutFieldFaithful
    · constructor
      · exact Nonempty.intro regularCauchyLocatedCutNontrivial
      · constructor
        · exact RegularCauchyLocatedCutTasteGate_single_carrier_alignment_decode
        · constructor
          · exact RegularCauchyLocatedCutTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact RegularCauchyLocatedCutTasteGate_single_carrier_alignment_injective heq
            · rfl

end BEDC.Derived.RegularCauchyLocatedCutUp
