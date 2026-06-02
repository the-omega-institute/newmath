import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConvexConjugateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConvexConjugateUp : Type where
  | mk : (F V P D E S H C Q N : BHist) → ConvexConjugateUp
  deriving DecidableEq

def convexConjugateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: convexConjugateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: convexConjugateEncodeBHist h

def convexConjugateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (convexConjugateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (convexConjugateDecodeBHist tail)

private theorem convexConjugate_decode_encode_bhist :
    ∀ h : BHist, convexConjugateDecodeBHist (convexConjugateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def convexConjugateFields : ConvexConjugateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConvexConjugateUp.mk F V P D E S H C Q N => [F, V, P, D, E, S, H, C, Q, N]

def convexConjugateToEventFlow : ConvexConjugateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (convexConjugateFields x).map convexConjugateEncodeBHist

private def convexConjugateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => convexConjugateEventAtDefault index rest

def convexConjugateFromEventFlow (ef : EventFlow) : Option ConvexConjugateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConvexConjugateUp.mk
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 0 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 1 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 2 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 3 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 4 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 5 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 6 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 7 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 8 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAtDefault 9 ef)))

private theorem convexConjugate_round_trip :
    ∀ x : ConvexConjugateUp,
      convexConjugateFromEventFlow (convexConjugateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F V P D E S H C Q N =>
      change
        some
          (ConvexConjugateUp.mk
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist F))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist V))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist P))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist D))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist E))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist S))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist H))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist C))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist Q))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist N))) =
          some (ConvexConjugateUp.mk F V P D E S H C Q N)
      rw [convexConjugate_decode_encode_bhist F,
        convexConjugate_decode_encode_bhist V,
        convexConjugate_decode_encode_bhist P,
        convexConjugate_decode_encode_bhist D,
        convexConjugate_decode_encode_bhist E,
        convexConjugate_decode_encode_bhist S,
        convexConjugate_decode_encode_bhist H,
        convexConjugate_decode_encode_bhist C,
        convexConjugate_decode_encode_bhist Q,
        convexConjugate_decode_encode_bhist N]

private theorem convexConjugateToEventFlow_injective {x y : ConvexConjugateUp} :
    convexConjugateToEventFlow x = convexConjugateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      convexConjugateFromEventFlow (convexConjugateToEventFlow x) =
        convexConjugateFromEventFlow (convexConjugateToEventFlow y) :=
    congrArg convexConjugateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (convexConjugate_round_trip x).symm
      (Eq.trans hread (convexConjugate_round_trip y)))

private theorem convexConjugate_fields_faithful :
    ∀ x y : ConvexConjugateUp, convexConjugateFields x = convexConjugateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk F1 V1 P1 D1 E1 S1 H1 C1 Q1 N1 =>
      cases y with
      | mk F2 V2 P2 D2 E2 S2 H2 C2 Q2 N2 =>
          injection h with hF t1
          injection t1 with hV t2
          injection t2 with hP t3
          injection t3 with hD t4
          injection t4 with hE t5
          injection t5 with hS t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hQ t9
          injection t9 with hN _
          subst hF
          subst hV
          subst hP
          subst hD
          subst hE
          subst hS
          subst hH
          subst hC
          subst hQ
          subst hN
          rfl

instance convexConjugateBHistCarrier : BHistCarrier ConvexConjugateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := convexConjugateToEventFlow
  fromEventFlow := convexConjugateFromEventFlow

instance convexConjugateChapterTasteGate : ChapterTasteGate ConvexConjugateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change convexConjugateFromEventFlow (convexConjugateToEventFlow x) = some x
    exact convexConjugate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (convexConjugateToEventFlow_injective heq)

instance convexConjugateFieldFaithful : FieldFaithful ConvexConjugateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := convexConjugateFields
  field_faithful := convexConjugate_fields_faithful

instance convexConjugateNontrivial : BEDC.Meta.TasteGate.Nontrivial ConvexConjugateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConvexConjugateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConvexConjugateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConvexConjugateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  convexConjugateChapterTasteGate

theorem ConvexConjugateTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ConvexConjugateUp) ∧
      Nonempty (ChapterTasteGate ConvexConjugateUp) ∧
        Nonempty (FieldFaithful ConvexConjugateUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial ConvexConjugateUp) ∧
            (∀ h : BHist, convexConjugateDecodeBHist (convexConjugateEncodeBHist h) = h) ∧
              (∀ x : ConvexConjugateUp,
                convexConjugateFromEventFlow (convexConjugateToEventFlow x) = some x) ∧
                (∀ x y : ConvexConjugateUp,
                  convexConjugateToEventFlow x = convexConjugateToEventFlow y → x = y) ∧
                  convexConjugateEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨convexConjugateBHistCarrier⟩,
      ⟨convexConjugateChapterTasteGate⟩,
      ⟨convexConjugateFieldFaithful⟩,
      ⟨convexConjugateNontrivial⟩,
      convexConjugate_decode_encode_bhist,
      convexConjugate_round_trip,
      (fun _ _ heq => convexConjugateToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ConvexConjugateUp
