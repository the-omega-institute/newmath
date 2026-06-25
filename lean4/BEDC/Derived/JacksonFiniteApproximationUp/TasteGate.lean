import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.JacksonFiniteApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive JacksonFiniteApproximationUp : Type where
  | mk (K F Omega D T PW Q E H C Pi N : BHist) : JacksonFiniteApproximationUp
  deriving DecidableEq

def jacksonFiniteApproximationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: jacksonFiniteApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: jacksonFiniteApproximationEncodeBHist h

def jacksonFiniteApproximationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (jacksonFiniteApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (jacksonFiniteApproximationDecodeBHist tail)

private theorem JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def jacksonFiniteApproximationToEventFlow : JacksonFiniteApproximationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | JacksonFiniteApproximationUp.mk K F Omega D T PW Q E H C Pi N =>
      [jacksonFiniteApproximationEncodeBHist K,
        jacksonFiniteApproximationEncodeBHist F,
        jacksonFiniteApproximationEncodeBHist Omega,
        jacksonFiniteApproximationEncodeBHist D,
        jacksonFiniteApproximationEncodeBHist T,
        jacksonFiniteApproximationEncodeBHist PW,
        jacksonFiniteApproximationEncodeBHist Q,
        jacksonFiniteApproximationEncodeBHist E,
        jacksonFiniteApproximationEncodeBHist H,
        jacksonFiniteApproximationEncodeBHist C,
        jacksonFiniteApproximationEncodeBHist Pi,
        jacksonFiniteApproximationEncodeBHist N]

private def jacksonFiniteApproximationEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => jacksonFiniteApproximationEventAtDefault index rest

def jacksonFiniteApproximationFromEventFlow
    (ef : EventFlow) : Option JacksonFiniteApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (JacksonFiniteApproximationUp.mk
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 0 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 1 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 2 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 3 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 4 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 5 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 6 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 7 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 8 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 9 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 10 ef))
      (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEventAtDefault 11 ef)))

private theorem JacksonFiniteApproximationTasteGate_single_carrier_alignment_round_trip
    (x : JacksonFiniteApproximationUp) :
    jacksonFiniteApproximationFromEventFlow (jacksonFiniteApproximationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F Omega D T PW Q E H C Pi N =>
      change
        some
          (JacksonFiniteApproximationUp.mk
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist K))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist F))
            (jacksonFiniteApproximationDecodeBHist
              (jacksonFiniteApproximationEncodeBHist Omega))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist D))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist T))
            (jacksonFiniteApproximationDecodeBHist
              (jacksonFiniteApproximationEncodeBHist PW))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist Q))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist E))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist H))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist C))
            (jacksonFiniteApproximationDecodeBHist
              (jacksonFiniteApproximationEncodeBHist Pi))
            (jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist N))) =
          some (JacksonFiniteApproximationUp.mk K F Omega D T PW Q E H C Pi N)
      rw [JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode K,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode F,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode Omega,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode D,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode T,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode PW,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode Q,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode E,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode H,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode C,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode Pi,
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode N]

private theorem JacksonFiniteApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : JacksonFiniteApproximationUp} :
    jacksonFiniteApproximationToEventFlow x = jacksonFiniteApproximationToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      jacksonFiniteApproximationFromEventFlow (jacksonFiniteApproximationToEventFlow x) =
        jacksonFiniteApproximationFromEventFlow (jacksonFiniteApproximationToEventFlow y) :=
    congrArg jacksonFiniteApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (JacksonFiniteApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (JacksonFiniteApproximationTasteGate_single_carrier_alignment_round_trip y)))

private def jacksonFiniteApproximationFields : JacksonFiniteApproximationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | JacksonFiniteApproximationUp.mk K F Omega D T PW Q E H C Pi N =>
      [K, F, Omega, D, T, PW, Q, E, H, C, Pi, N]

private theorem JacksonFiniteApproximationTasteGate_single_carrier_alignment_fields :
    forall x y : JacksonFiniteApproximationUp, jacksonFiniteApproximationFields x =
      jacksonFiniteApproximationFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 Omega1 D1 T1 PW1 Q1 E1 H1 C1 Pi1 N1 =>
      cases y with
      | mk K2 F2 Omega2 D2 T2 PW2 Q2 E2 H2 C2 Pi2 N2 =>
          cases hfields
          rfl

instance jacksonFiniteApproximationBHistCarrier :
    BHistCarrier JacksonFiniteApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := jacksonFiniteApproximationToEventFlow
  fromEventFlow := jacksonFiniteApproximationFromEventFlow

instance jacksonFiniteApproximationChapterTasteGate :
    ChapterTasteGate JacksonFiniteApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      jacksonFiniteApproximationFromEventFlow (jacksonFiniteApproximationToEventFlow x) =
        some x
    exact JacksonFiniteApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (JacksonFiniteApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance jacksonFiniteApproximationFieldFaithful :
    FieldFaithful JacksonFiniteApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := jacksonFiniteApproximationFields
  field_faithful := JacksonFiniteApproximationTasteGate_single_carrier_alignment_fields

instance jacksonFiniteApproximationNontrivial : Nontrivial JacksonFiniteApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨JacksonFiniteApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      JacksonFiniteApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate JacksonFiniteApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  jacksonFiniteApproximationChapterTasteGate

theorem JacksonFiniteApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        jacksonFiniteApproximationDecodeBHist (jacksonFiniteApproximationEncodeBHist h) = h) ∧
      (∀ x : JacksonFiniteApproximationUp,
        jacksonFiniteApproximationFromEventFlow (jacksonFiniteApproximationToEventFlow x) =
          some x) ∧
        (∀ x y : JacksonFiniteApproximationUp,
          jacksonFiniteApproximationToEventFlow x =
            jacksonFiniteApproximationToEventFlow y -> x = y) ∧
          jacksonFiniteApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨JacksonFiniteApproximationTasteGate_single_carrier_alignment_decode,
      JacksonFiniteApproximationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        JacksonFiniteApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.JacksonFiniteApproximationUp
