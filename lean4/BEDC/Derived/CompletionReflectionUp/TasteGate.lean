import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionReflectionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionReflectionUp : Type where
  | mk : (C U H D Q A S T K P N : BHist) → CompletionReflectionUp
  deriving DecidableEq

def completionReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionReflectionEncodeBHist h

def completionReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionReflectionDecodeBHist tail)

private theorem completionReflection_decode_encode :
    ∀ h : BHist, completionReflectionDecodeBHist (completionReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionReflectionFields : CompletionReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionReflectionUp.mk C U H D Q A S T K P N => [C, U, H, D, Q, A, S, T, K, P, N]

def completionReflectionToEventFlow : CompletionReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionReflectionFields x).map completionReflectionEncodeBHist

def completionReflectionFromEventFlow : EventFlow → Option CompletionReflectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | C :: rest0 =>
      match rest0 with
      | [] => none
      | U :: rest1 =>
          match rest1 with
          | [] => none
          | H :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | S :: rest6 =>
                              match rest6 with
                              | [] => none
                              | T :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | K :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CompletionReflectionUp.mk
                                                      (completionReflectionDecodeBHist C)
                                                      (completionReflectionDecodeBHist U)
                                                      (completionReflectionDecodeBHist H)
                                                      (completionReflectionDecodeBHist D)
                                                      (completionReflectionDecodeBHist Q)
                                                      (completionReflectionDecodeBHist A)
                                                      (completionReflectionDecodeBHist S)
                                                      (completionReflectionDecodeBHist T)
                                                      (completionReflectionDecodeBHist K)
                                                      (completionReflectionDecodeBHist P)
                                                      (completionReflectionDecodeBHist N))
                                              | _ :: _ => none

private theorem completionReflection_round_trip :
    ∀ x : CompletionReflectionUp,
      completionReflectionFromEventFlow (completionReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C U H D Q A S T K P N =>
      change
        some
          (CompletionReflectionUp.mk
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist C))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist U))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist H))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist D))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist Q))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist A))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist S))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist T))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist K))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist P))
            (completionReflectionDecodeBHist (completionReflectionEncodeBHist N))) =
          some (CompletionReflectionUp.mk C U H D Q A S T K P N)
      rw [completionReflection_decode_encode C, completionReflection_decode_encode U,
        completionReflection_decode_encode H, completionReflection_decode_encode D,
        completionReflection_decode_encode Q, completionReflection_decode_encode A,
        completionReflection_decode_encode S, completionReflection_decode_encode T,
        completionReflection_decode_encode K, completionReflection_decode_encode P,
        completionReflection_decode_encode N]

private theorem completionReflectionToEventFlow_injective
    {x y : CompletionReflectionUp} :
    completionReflectionToEventFlow x = completionReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionReflectionFromEventFlow (completionReflectionToEventFlow x) =
        completionReflectionFromEventFlow (completionReflectionToEventFlow y) :=
    congrArg completionReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completionReflection_round_trip x).symm
      (Eq.trans hread (completionReflection_round_trip y)))

private theorem completionReflection_fields_faithful :
    ∀ x y : CompletionReflectionUp,
      completionReflectionFields x = completionReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk C1 U1 H1 D1 Q1 A1 S1 T1 K1 P1 N1 =>
      cases y with
      | mk C2 U2 H2 D2 Q2 A2 S2 T2 K2 P2 N2 =>
          injection h with hC t1
          injection t1 with hU t2
          injection t2 with hH t3
          injection t3 with hD t4
          injection t4 with hQ t5
          injection t5 with hA t6
          injection t6 with hS t7
          injection t7 with hT t8
          injection t8 with hK t9
          injection t9 with hP t10
          injection t10 with hN _
          subst hC
          subst hU
          subst hH
          subst hD
          subst hQ
          subst hA
          subst hS
          subst hT
          subst hK
          subst hP
          subst hN
          rfl

instance completionReflectionBHistCarrier : BHistCarrier CompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionReflectionToEventFlow
  fromEventFlow := completionReflectionFromEventFlow

instance completionReflectionChapterTasteGate :
    ChapterTasteGate CompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionReflectionFromEventFlow (completionReflectionToEventFlow x) = some x
    exact completionReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completionReflectionToEventFlow_injective heq)

instance completionReflectionFieldFaithful : FieldFaithful CompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionReflectionFields
  field_faithful := completionReflection_fields_faithful

instance completionReflectionNontrivial : Nontrivial CompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionReflectionChapterTasteGate

theorem CompletionReflectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompletionReflectionUp) ∧
      Nonempty (FieldFaithful CompletionReflectionUp) ∧
      Nonempty (Nontrivial CompletionReflectionUp) ∧
      (∀ h : BHist, completionReflectionDecodeBHist (completionReflectionEncodeBHist h) = h) ∧
      (∀ x : CompletionReflectionUp,
        completionReflectionFromEventFlow (completionReflectionToEventFlow x) = some x) ∧
      (∀ x y : CompletionReflectionUp,
        completionReflectionToEventFlow x = completionReflectionToEventFlow y → x = y) ∧
      completionReflectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨completionReflectionChapterTasteGate⟩, ⟨completionReflectionFieldFaithful⟩,
      ⟨completionReflectionNontrivial⟩, completionReflection_decode_encode,
      completionReflection_round_trip,
      fun _ _ heq => completionReflectionToEventFlow_injective heq, rfl⟩

end BEDC.Derived.CompletionReflectionUp.TasteGate
