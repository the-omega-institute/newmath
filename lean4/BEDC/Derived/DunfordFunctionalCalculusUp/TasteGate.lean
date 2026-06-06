import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DunfordFunctionalCalculusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DunfordFunctionalCalculusUp : Type where
  | mk (A T Gamma Omega R I Q S H C P N : BHist) : DunfordFunctionalCalculusUp
  deriving DecidableEq

def dunfordFunctionalCalculusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dunfordFunctionalCalculusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dunfordFunctionalCalculusEncodeBHist h

def dunfordFunctionalCalculusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dunfordFunctionalCalculusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dunfordFunctionalCalculusDecodeBHist tail)

private theorem dunfordFunctionalCalculus_decode_encode_bhist :
    ∀ h : BHist, dunfordFunctionalCalculusDecodeBHist
      (dunfordFunctionalCalculusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dunfordFunctionalCalculusFields : DunfordFunctionalCalculusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DunfordFunctionalCalculusUp.mk A T Gamma Omega R I Q S H C P N =>
      [A, T, Gamma, Omega, R, I, Q, S, H, C, P, N]

def dunfordFunctionalCalculusToEventFlow : DunfordFunctionalCalculusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dunfordFunctionalCalculusFields x).map dunfordFunctionalCalculusEncodeBHist

private def dunfordFunctionalCalculusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dunfordFunctionalCalculusEventAtDefault index rest

def dunfordFunctionalCalculusFromEventFlow
    (ef : EventFlow) : Option DunfordFunctionalCalculusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DunfordFunctionalCalculusUp.mk
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 0 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 1 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 2 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 3 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 4 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 5 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 6 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 7 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 8 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 9 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 10 ef))
      (dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEventAtDefault 11 ef)))

private theorem dunfordFunctionalCalculus_round_trip :
    ∀ x : DunfordFunctionalCalculusUp,
      dunfordFunctionalCalculusFromEventFlow
        (dunfordFunctionalCalculusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A T Gamma Omega R I Q S H C P N =>
      change
        some
          (DunfordFunctionalCalculusUp.mk
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist A))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist T))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist Gamma))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist Omega))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist R))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist I))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist Q))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist S))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist H))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist C))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist P))
            (dunfordFunctionalCalculusDecodeBHist
              (dunfordFunctionalCalculusEncodeBHist N))) =
          some (DunfordFunctionalCalculusUp.mk A T Gamma Omega R I Q S H C P N)
      rw [dunfordFunctionalCalculus_decode_encode_bhist A,
        dunfordFunctionalCalculus_decode_encode_bhist T,
        dunfordFunctionalCalculus_decode_encode_bhist Gamma,
        dunfordFunctionalCalculus_decode_encode_bhist Omega,
        dunfordFunctionalCalculus_decode_encode_bhist R,
        dunfordFunctionalCalculus_decode_encode_bhist I,
        dunfordFunctionalCalculus_decode_encode_bhist Q,
        dunfordFunctionalCalculus_decode_encode_bhist S,
        dunfordFunctionalCalculus_decode_encode_bhist H,
        dunfordFunctionalCalculus_decode_encode_bhist C,
        dunfordFunctionalCalculus_decode_encode_bhist P,
        dunfordFunctionalCalculus_decode_encode_bhist N]

private theorem dunfordFunctionalCalculusToEventFlow_injective
    {x y : DunfordFunctionalCalculusUp} :
    dunfordFunctionalCalculusToEventFlow x = dunfordFunctionalCalculusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dunfordFunctionalCalculusFromEventFlow (dunfordFunctionalCalculusToEventFlow x) =
        dunfordFunctionalCalculusFromEventFlow (dunfordFunctionalCalculusToEventFlow y) :=
    congrArg dunfordFunctionalCalculusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dunfordFunctionalCalculus_round_trip x).symm
      (Eq.trans hread (dunfordFunctionalCalculus_round_trip y)))

private theorem dunfordFunctionalCalculus_fields_faithful :
    ∀ x y : DunfordFunctionalCalculusUp,
      dunfordFunctionalCalculusFields x = dunfordFunctionalCalculusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 T1 Gamma1 Omega1 R1 I1 Q1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 T2 Gamma2 Omega2 R2 I2 Q2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dunfordFunctionalCalculusBHistCarrier :
    BHistCarrier DunfordFunctionalCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dunfordFunctionalCalculusToEventFlow
  fromEventFlow := dunfordFunctionalCalculusFromEventFlow

instance dunfordFunctionalCalculusChapterTasteGate :
    ChapterTasteGate DunfordFunctionalCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dunfordFunctionalCalculusFromEventFlow (dunfordFunctionalCalculusToEventFlow x) =
        some x
    exact dunfordFunctionalCalculus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dunfordFunctionalCalculusToEventFlow_injective heq)

instance dunfordFunctionalCalculusFieldFaithful :
    FieldFaithful DunfordFunctionalCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dunfordFunctionalCalculusFields
  field_faithful := dunfordFunctionalCalculus_fields_faithful

instance dunfordFunctionalCalculusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DunfordFunctionalCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DunfordFunctionalCalculusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DunfordFunctionalCalculusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DunfordFunctionalCalculusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dunfordFunctionalCalculusChapterTasteGate

theorem DunfordFunctionalCalculusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DunfordFunctionalCalculusUp) ∧
      Nonempty (FieldFaithful DunfordFunctionalCalculusUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DunfordFunctionalCalculusUp) ∧
          (∀ h : BHist,
            dunfordFunctionalCalculusDecodeBHist (dunfordFunctionalCalculusEncodeBHist h) =
              h) ∧
            (∀ x : DunfordFunctionalCalculusUp,
              dunfordFunctionalCalculusFromEventFlow
                  (dunfordFunctionalCalculusToEventFlow x) =
                some x) ∧
              (∀ x y : DunfordFunctionalCalculusUp,
                dunfordFunctionalCalculusToEventFlow x =
                    dunfordFunctionalCalculusToEventFlow y →
                  x = y) ∧
                dunfordFunctionalCalculusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨dunfordFunctionalCalculusChapterTasteGate⟩,
      ⟨dunfordFunctionalCalculusFieldFaithful⟩,
      ⟨dunfordFunctionalCalculusNontrivial⟩,
      dunfordFunctionalCalculus_decode_encode_bhist,
      dunfordFunctionalCalculus_round_trip,
      (by
        intro x y heq
        exact dunfordFunctionalCalculusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DunfordFunctionalCalculusUp
