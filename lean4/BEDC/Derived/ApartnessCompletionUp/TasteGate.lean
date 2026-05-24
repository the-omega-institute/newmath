import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApartnessCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApartnessCompletionUp : Type where
  | mk (X Q M S R D E H C P N : BHist) : ApartnessCompletionUp
  deriving DecidableEq

def apartnessCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apartnessCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apartnessCompletionEncodeBHist h

def apartnessCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apartnessCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apartnessCompletionDecodeBHist tail)

private theorem apartnessCompletion_decode_encode :
    ∀ h : BHist, apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apartnessCompletionFields : ApartnessCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessCompletionUp.mk X Q M S R D E H C P N => [X, Q, M, S, R, D, E, H, C, P, N]

def apartnessCompletionToEventFlow : ApartnessCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (apartnessCompletionFields x).map apartnessCompletionEncodeBHist

def apartnessCompletionFromEventFlow (flow : EventFlow) : Option ApartnessCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ApartnessCompletionUp.mk
                                                      (apartnessCompletionDecodeBHist X)
                                                      (apartnessCompletionDecodeBHist Q)
                                                      (apartnessCompletionDecodeBHist M)
                                                      (apartnessCompletionDecodeBHist S)
                                                      (apartnessCompletionDecodeBHist R)
                                                      (apartnessCompletionDecodeBHist D)
                                                      (apartnessCompletionDecodeBHist E)
                                                      (apartnessCompletionDecodeBHist H)
                                                      (apartnessCompletionDecodeBHist C)
                                                      (apartnessCompletionDecodeBHist P)
                                                      (apartnessCompletionDecodeBHist N))
                                              | _ :: _ => none

private theorem apartnessCompletion_round_trip :
    ∀ x : ApartnessCompletionUp,
      apartnessCompletionFromEventFlow (apartnessCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Q M S R D E H C P N =>
      change
        some
          (ApartnessCompletionUp.mk
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist X))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist Q))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist M))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist S))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist R))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist D))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist E))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist H))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist C))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist P))
            (apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist N))) =
          some (ApartnessCompletionUp.mk X Q M S R D E H C P N)
      rw [apartnessCompletion_decode_encode X, apartnessCompletion_decode_encode Q,
        apartnessCompletion_decode_encode M, apartnessCompletion_decode_encode S,
        apartnessCompletion_decode_encode R, apartnessCompletion_decode_encode D,
        apartnessCompletion_decode_encode E, apartnessCompletion_decode_encode H,
        apartnessCompletion_decode_encode C, apartnessCompletion_decode_encode P,
        apartnessCompletion_decode_encode N]

private theorem apartnessCompletionToEventFlow_injective {x y : ApartnessCompletionUp} :
    apartnessCompletionToEventFlow x = apartnessCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apartnessCompletionFromEventFlow (apartnessCompletionToEventFlow x) =
        apartnessCompletionFromEventFlow (apartnessCompletionToEventFlow y) :=
    congrArg apartnessCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apartnessCompletion_round_trip x).symm
      (Eq.trans hread (apartnessCompletion_round_trip y)))

private theorem apartnessCompletion_fields_faithful :
    ∀ x y : ApartnessCompletionUp, apartnessCompletionFields x = apartnessCompletionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Q1 M1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Q2 M2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance apartnessCompletionBHistCarrier : BHistCarrier ApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apartnessCompletionToEventFlow
  fromEventFlow := apartnessCompletionFromEventFlow

instance apartnessCompletionChapterTasteGate :
    ChapterTasteGate ApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apartnessCompletionFromEventFlow (apartnessCompletionToEventFlow x) = some x
    exact apartnessCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apartnessCompletionToEventFlow_injective heq)

instance apartnessCompletionFieldFaithful : FieldFaithful ApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apartnessCompletionFields
  field_faithful := apartnessCompletion_fields_faithful

instance apartnessCompletionNontrivial : Nontrivial ApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApartnessCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApartnessCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApartnessCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apartnessCompletionChapterTasteGate

theorem ApartnessCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ApartnessCompletionUp) ∧
      Nonempty (FieldFaithful ApartnessCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ApartnessCompletionUp) ∧
          (∀ h : BHist, apartnessCompletionDecodeBHist (apartnessCompletionEncodeBHist h) = h) ∧
            (∀ x : ApartnessCompletionUp,
              apartnessCompletionFromEventFlow (apartnessCompletionToEventFlow x) = some x) ∧
              (∀ x y : ApartnessCompletionUp,
                apartnessCompletionToEventFlow x = apartnessCompletionToEventFlow y → x = y) ∧
                apartnessCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨apartnessCompletionChapterTasteGate⟩,
      ⟨apartnessCompletionFieldFaithful⟩,
      ⟨apartnessCompletionNontrivial⟩,
      apartnessCompletion_decode_encode,
      apartnessCompletion_round_trip,
      fun _ _ heq => apartnessCompletionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ApartnessCompletionUp
