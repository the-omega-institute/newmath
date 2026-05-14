import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverDirectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverDirectionUp : Type where
  | mk : (R T U L B H C P N : BHist) → ObserverDirectionUp
  deriving DecidableEq

def observerDirectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerDirectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerDirectionEncodeBHist h

def observerDirectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerDirectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerDirectionDecodeBHist tail)

private theorem observerDirectionDecode_encode_bhist :
    ∀ h : BHist, observerDirectionDecodeBHist (observerDirectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observerDirectionToEventFlow : ObserverDirectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverDirectionUp.mk R T U L B H C P N =>
      [[BMark.b0],
        observerDirectionEncodeBHist R,
        [BMark.b1, BMark.b0],
        observerDirectionEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerDirectionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerDirectionEncodeBHist N]

private def observerDirectionDecodePacket
    (R T U L B H C P N : RawEvent) : ObserverDirectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ObserverDirectionUp.mk
    (observerDirectionDecodeBHist R)
    (observerDirectionDecodeBHist T)
    (observerDirectionDecodeBHist U)
    (observerDirectionDecodeBHist L)
    (observerDirectionDecodeBHist B)
    (observerDirectionDecodeBHist H)
    (observerDirectionDecodeBHist C)
    (observerDirectionDecodeBHist P)
    (observerDirectionDecodeBHist N)

def observerDirectionFromEventFlow : EventFlow → Option ObserverDirectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | U :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | B :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (observerDirectionDecodePacket
                                                                                  R T U L B H C P N)
                                                                          | _ :: _ => none

private theorem observerDirection_round_trip :
    ∀ x : ObserverDirectionUp,
      observerDirectionFromEventFlow (observerDirectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R T U L B H C P N =>
      change
        some
            (observerDirectionDecodePacket
              (observerDirectionEncodeBHist R)
              (observerDirectionEncodeBHist T)
              (observerDirectionEncodeBHist U)
              (observerDirectionEncodeBHist L)
              (observerDirectionEncodeBHist B)
              (observerDirectionEncodeBHist H)
              (observerDirectionEncodeBHist C)
              (observerDirectionEncodeBHist P)
              (observerDirectionEncodeBHist N)) =
          some (ObserverDirectionUp.mk R T U L B H C P N)
      unfold observerDirectionDecodePacket
      rw [observerDirectionDecode_encode_bhist R,
        observerDirectionDecode_encode_bhist T,
        observerDirectionDecode_encode_bhist U,
        observerDirectionDecode_encode_bhist L,
        observerDirectionDecode_encode_bhist B,
        observerDirectionDecode_encode_bhist H,
        observerDirectionDecode_encode_bhist C,
        observerDirectionDecode_encode_bhist P,
        observerDirectionDecode_encode_bhist N]

private theorem observerDirectionToEventFlow_injective {x y : ObserverDirectionUp} :
    observerDirectionToEventFlow x = observerDirectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerDirectionFromEventFlow (observerDirectionToEventFlow x) =
        observerDirectionFromEventFlow (observerDirectionToEventFlow y) :=
    congrArg observerDirectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerDirection_round_trip x).symm
      (Eq.trans hread (observerDirection_round_trip y)))

instance observerDirectionBHistCarrier : BHistCarrier ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerDirectionToEventFlow
  fromEventFlow := observerDirectionFromEventFlow

instance observerDirectionChapterTasteGate : ChapterTasteGate ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerDirectionFromEventFlow (observerDirectionToEventFlow x) = some x
    exact observerDirection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerDirectionToEventFlow_injective heq)

instance observerDirectionFieldFaithful : FieldFaithful ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverDirectionUp.mk R T U L B H C P N => [R, T, U, L, B, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk R₁ T₁ U₁ L₁ B₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk R₂ T₂ U₂ L₂ B₂ H₂ C₂ P₂ N₂ =>
            injection h with hR t1
            injection t1 with hT t2
            injection t2 with hU t3
            injection t3 with hL t4
            injection t4 with hB t5
            injection t5 with hH t6
            injection t6 with hC t7
            injection t7 with hP t8
            injection t8 with hN _
            subst hR
            subst hT
            subst hU
            subst hL
            subst hB
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance observerDirectionNontrivial : Nontrivial ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverDirectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverDirectionUp.mk BHist.Empty BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverDirectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerDirectionChapterTasteGate

theorem ObserverDirectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerDirectionDecodeBHist (observerDirectionEncodeBHist h) = h) ∧
      (∀ x : ObserverDirectionUp,
        observerDirectionFromEventFlow (observerDirectionToEventFlow x) = some x) ∧
        (∀ x y : ObserverDirectionUp,
          observerDirectionToEventFlow x = observerDirectionToEventFlow y → x = y) ∧
          Nonempty (Nontrivial ObserverDirectionUp) ∧
            Nonempty (FieldFaithful ObserverDirectionUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerDirectionDecode_encode_bhist
  · constructor
    · exact observerDirection_round_trip
    · constructor
      · intro x y heq
        exact observerDirectionToEventFlow_injective heq
      · constructor
        · exact ⟨observerDirectionNontrivial⟩
        · exact ⟨observerDirectionFieldFaithful⟩

namespace TasteGate

theorem ObserverDirectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerDirectionDecodeBHist (observerDirectionEncodeBHist h) = h) ∧
      (∀ x : ObserverDirectionUp,
        observerDirectionFromEventFlow (observerDirectionToEventFlow x) = some x) ∧
        (∀ x y : ObserverDirectionUp,
          observerDirectionToEventFlow x = observerDirectionToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate ObserverDirectionUp) ∧
            Nonempty (FieldFaithful ObserverDirectionUp) ∧
              Nonempty (Nontrivial ObserverDirectionUp) ∧
                observerDirectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerDirectionDecode_encode_bhist
  · constructor
    · exact observerDirection_round_trip
    · constructor
      · intro x y heq
        exact observerDirectionToEventFlow_injective heq
      · constructor
        · exact ⟨observerDirectionChapterTasteGate⟩
        · constructor
          · exact ⟨observerDirectionFieldFaithful⟩
          · constructor
            · exact ⟨observerDirectionNontrivial⟩
            · rfl

end TasteGate

end BEDC.Derived.ObserverDirectionUp
