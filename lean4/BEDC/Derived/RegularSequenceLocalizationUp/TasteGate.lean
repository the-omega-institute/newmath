import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularSequenceLocalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularSequenceLocalizationUp : Type where
  | mk (a rho W Q R H C P N : BHist) : RegularSequenceLocalizationUp

def regularSequenceLocalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularSequenceLocalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularSequenceLocalizationEncodeBHist h

def regularSequenceLocalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularSequenceLocalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularSequenceLocalizationDecodeBHist tail)

private theorem RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularSequenceLocalizationFields : RegularSequenceLocalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularSequenceLocalizationUp.mk a rho W Q R H C P N => [a, rho, W, Q, R, H, C, P, N]

def regularSequenceLocalizationToEventFlow : RegularSequenceLocalizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularSequenceLocalizationFields x).map regularSequenceLocalizationEncodeBHist

private def regularSequenceLocalizationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularSequenceLocalizationEventAtDefault index rest

def regularSequenceLocalizationFromEventFlow
    (ef : EventFlow) : Option RegularSequenceLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularSequenceLocalizationUp.mk
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 0 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 1 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 2 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 3 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 4 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 5 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 6 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 7 ef))
      (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEventAtDefault 8 ef)))

private theorem RegularSequenceLocalizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularSequenceLocalizationUp,
      regularSequenceLocalizationFromEventFlow
        (regularSequenceLocalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a rho W Q R H C P N =>
      change
        some
          (RegularSequenceLocalizationUp.mk
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist a))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist rho))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist W))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist Q))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist R))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist H))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist C))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist P))
            (regularSequenceLocalizationDecodeBHist (regularSequenceLocalizationEncodeBHist N))) =
          some (RegularSequenceLocalizationUp.mk a rho W Q R H C P N)
      rw [RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode a,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode rho,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode W,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode Q,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode R,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode H,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode C,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode P,
        RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode N]

private theorem RegularSequenceLocalizationTasteGate_single_carrier_alignment_injective
    {x y : RegularSequenceLocalizationUp} :
    regularSequenceLocalizationToEventFlow x = regularSequenceLocalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularSequenceLocalizationFromEventFlow (regularSequenceLocalizationToEventFlow x) =
        regularSequenceLocalizationFromEventFlow (regularSequenceLocalizationToEventFlow y) :=
    congrArg regularSequenceLocalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularSequenceLocalizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularSequenceLocalizationTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularSequenceLocalizationTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularSequenceLocalizationUp,
      regularSequenceLocalizationFields x = regularSequenceLocalizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk a1 rho1 W1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk a2 rho2 W2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularSequenceLocalizationBHistCarrier :
    BHistCarrier RegularSequenceLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularSequenceLocalizationToEventFlow
  fromEventFlow := regularSequenceLocalizationFromEventFlow

instance regularSequenceLocalizationChapterTasteGate :
    ChapterTasteGate RegularSequenceLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularSequenceLocalizationFromEventFlow (regularSequenceLocalizationToEventFlow x) =
        some x
    exact RegularSequenceLocalizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularSequenceLocalizationTasteGate_single_carrier_alignment_injective heq)

instance regularSequenceLocalizationFieldFaithful :
    FieldFaithful RegularSequenceLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularSequenceLocalizationFields
  field_faithful := RegularSequenceLocalizationTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate RegularSequenceLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularSequenceLocalizationChapterTasteGate

theorem RegularSequenceLocalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularSequenceLocalizationDecodeBHist
      (regularSequenceLocalizationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularSequenceLocalizationUp) ∧
        Nonempty (ChapterTasteGate RegularSequenceLocalizationUp) ∧
          regularSequenceLocalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨RegularSequenceLocalizationTasteGate_single_carrier_alignment_decode,
      ⟨regularSequenceLocalizationBHistCarrier⟩,
      ⟨regularSequenceLocalizationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularSequenceLocalizationUp
