import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusIndependenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusIndependenceUp : Type where
  | mk (R S0 S1 D0 D1 J A H C P N : BHist) : RegularCauchyModulusIndependenceUp
  deriving DecidableEq

def regularCauchyModulusIndependenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusIndependenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusIndependenceEncodeBHist h

def regularCauchyModulusIndependenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusIndependenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusIndependenceDecodeBHist tail)

private theorem regularCauchyModulusIndependence_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyModulusIndependenceDecodeBHist
          (regularCauchyModulusIndependenceEncodeBHist h) =
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

def regularCauchyModulusIndependenceToEventFlow :
    RegularCauchyModulusIndependenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusIndependenceUp.mk R S0 S1 D0 D1 J A H C P N =>
      [regularCauchyModulusIndependenceEncodeBHist R,
        regularCauchyModulusIndependenceEncodeBHist S0,
        regularCauchyModulusIndependenceEncodeBHist S1,
        regularCauchyModulusIndependenceEncodeBHist D0,
        regularCauchyModulusIndependenceEncodeBHist D1,
        regularCauchyModulusIndependenceEncodeBHist J,
        regularCauchyModulusIndependenceEncodeBHist A,
        regularCauchyModulusIndependenceEncodeBHist H,
        regularCauchyModulusIndependenceEncodeBHist C,
        regularCauchyModulusIndependenceEncodeBHist P,
        regularCauchyModulusIndependenceEncodeBHist N]

private def regularCauchyModulusIndependenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyModulusIndependenceEventAtDefault index rest

def regularCauchyModulusIndependenceFromEventFlow
    (ef : EventFlow) : Option RegularCauchyModulusIndependenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyModulusIndependenceUp.mk
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 0 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 1 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 2 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 3 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 4 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 5 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 6 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 7 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 8 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 9 ef))
      (regularCauchyModulusIndependenceDecodeBHist
        (regularCauchyModulusIndependenceEventAtDefault 10 ef)))

private theorem regularCauchyModulusIndependence_round_trip :
    ∀ x : RegularCauchyModulusIndependenceUp,
      regularCauchyModulusIndependenceFromEventFlow
          (regularCauchyModulusIndependenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S0 S1 D0 D1 J A H C P N =>
      change
        some
            (RegularCauchyModulusIndependenceUp.mk
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist R))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist S0))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist S1))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist D0))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist D1))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist J))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist A))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist H))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist C))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist P))
              (regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist N))) =
          some (RegularCauchyModulusIndependenceUp.mk R S0 S1 D0 D1 J A H C P N)
      rw [regularCauchyModulusIndependence_decode_encode_bhist R,
        regularCauchyModulusIndependence_decode_encode_bhist S0,
        regularCauchyModulusIndependence_decode_encode_bhist S1,
        regularCauchyModulusIndependence_decode_encode_bhist D0,
        regularCauchyModulusIndependence_decode_encode_bhist D1,
        regularCauchyModulusIndependence_decode_encode_bhist J,
        regularCauchyModulusIndependence_decode_encode_bhist A,
        regularCauchyModulusIndependence_decode_encode_bhist H,
        regularCauchyModulusIndependence_decode_encode_bhist C,
        regularCauchyModulusIndependence_decode_encode_bhist P,
        regularCauchyModulusIndependence_decode_encode_bhist N]

private theorem regularCauchyModulusIndependenceToEventFlow_injective
    {x y : RegularCauchyModulusIndependenceUp} :
    regularCauchyModulusIndependenceToEventFlow x =
        regularCauchyModulusIndependenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyModulusIndependenceFromEventFlow
          (regularCauchyModulusIndependenceToEventFlow x) =
        regularCauchyModulusIndependenceFromEventFlow
          (regularCauchyModulusIndependenceToEventFlow y) :=
    congrArg regularCauchyModulusIndependenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyModulusIndependence_round_trip x).symm
      (Eq.trans hread (regularCauchyModulusIndependence_round_trip y)))

def regularCauchyModulusIndependenceFields :
    RegularCauchyModulusIndependenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusIndependenceUp.mk R S0 S1 D0 D1 J A H C P N =>
      [R, S0, S1, D0, D1, J, A, H, C, P, N]

private theorem regularCauchyModulusIndependence_fields_faithful :
    ∀ x y : RegularCauchyModulusIndependenceUp,
      regularCauchyModulusIndependenceFields x =
          regularCauchyModulusIndependenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk R S0 S1 D0 D1 J A H C P N =>
      cases y with
      | mk R' S0' S1' D0' D1' J' A' H' C' P' N' =>
          simp only [regularCauchyModulusIndependenceFields] at h
          cases h
          rfl

instance regularCauchyModulusIndependenceBHistCarrier :
    BHistCarrier RegularCauchyModulusIndependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusIndependenceToEventFlow
  fromEventFlow := regularCauchyModulusIndependenceFromEventFlow

instance regularCauchyModulusIndependenceChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusIndependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusIndependenceFromEventFlow
          (regularCauchyModulusIndependenceToEventFlow x) =
        some x
    exact regularCauchyModulusIndependence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyModulusIndependenceToEventFlow_injective heq)

instance regularCauchyModulusIndependenceFieldFaithful :
    FieldFaithful RegularCauchyModulusIndependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyModulusIndependenceFields
  field_faithful := regularCauchyModulusIndependence_fields_faithful

instance regularCauchyModulusIndependenceNontrivial :
    Nontrivial RegularCauchyModulusIndependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyModulusIndependenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyModulusIndependenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyModulusIndependenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyModulusIndependenceChapterTasteGate

theorem RegularCauchyModulusIndependenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyModulusIndependenceUp) ∧
      Nonempty (FieldFaithful RegularCauchyModulusIndependenceUp) ∧
        Nonempty (Nontrivial RegularCauchyModulusIndependenceUp) ∧
          (∀ h : BHist,
            regularCauchyModulusIndependenceDecodeBHist
                (regularCauchyModulusIndependenceEncodeBHist h) =
              h) ∧
            (∀ x : RegularCauchyModulusIndependenceUp,
              regularCauchyModulusIndependenceFromEventFlow
                  (regularCauchyModulusIndependenceToEventFlow x) =
                some x) ∧
              regularCauchyModulusIndependenceEncodeBHist BHist.Empty =
                ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyModulusIndependenceChapterTasteGate⟩,
      ⟨regularCauchyModulusIndependenceFieldFaithful⟩,
      ⟨regularCauchyModulusIndependenceNontrivial⟩,
      regularCauchyModulusIndependence_decode_encode_bhist,
      regularCauchyModulusIndependence_round_trip,
      rfl⟩

end BEDC.Derived.RegularCauchyModulusIndependenceUp
