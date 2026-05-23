import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalNestLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalNestLimitUp : Type where
  | mk (I D S R E M H C P N : BHist) : BishopIntervalNestLimitUp
  deriving DecidableEq

def bishopIntervalNestLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalNestLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalNestLimitEncodeBHist h

def bishopIntervalNestLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalNestLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalNestLimitDecodeBHist tail)

private theorem bishopIntervalNestLimit_decode_encode :
    ∀ h : BHist, bishopIntervalNestLimitDecodeBHist
      (bishopIntervalNestLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopIntervalNestLimitFields : BishopIntervalNestLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalNestLimitUp.mk I D S R E M H C P N => [I, D, S, R, E, M, H, C, P, N]

def bishopIntervalNestLimitToEventFlow : BishopIntervalNestLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalNestLimitUp.mk I D S R E M H C P N =>
      [bishopIntervalNestLimitEncodeBHist I, bishopIntervalNestLimitEncodeBHist D,
        bishopIntervalNestLimitEncodeBHist S, bishopIntervalNestLimitEncodeBHist R,
        bishopIntervalNestLimitEncodeBHist E, bishopIntervalNestLimitEncodeBHist M,
        bishopIntervalNestLimitEncodeBHist H, bishopIntervalNestLimitEncodeBHist C,
        bishopIntervalNestLimitEncodeBHist P, bishopIntervalNestLimitEncodeBHist N]

def bishopIntervalNestLimitFromEventFlow : EventFlow → Option BishopIntervalNestLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | M :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (BishopIntervalNestLimitUp.mk
                                                  (bishopIntervalNestLimitDecodeBHist I)
                                                  (bishopIntervalNestLimitDecodeBHist D)
                                                  (bishopIntervalNestLimitDecodeBHist S)
                                                  (bishopIntervalNestLimitDecodeBHist R)
                                                  (bishopIntervalNestLimitDecodeBHist E)
                                                  (bishopIntervalNestLimitDecodeBHist M)
                                                  (bishopIntervalNestLimitDecodeBHist H)
                                                  (bishopIntervalNestLimitDecodeBHist C)
                                                  (bishopIntervalNestLimitDecodeBHist P)
                                                  (bishopIntervalNestLimitDecodeBHist N))
                                          | _ :: _ => none

private theorem bishopIntervalNestLimit_round_trip :
    ∀ x : BishopIntervalNestLimitUp,
      bishopIntervalNestLimitFromEventFlow (bishopIntervalNestLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D S R E M H C P N =>
      rw [bishopIntervalNestLimitToEventFlow, bishopIntervalNestLimitFromEventFlow,
        bishopIntervalNestLimit_decode_encode I, bishopIntervalNestLimit_decode_encode D,
        bishopIntervalNestLimit_decode_encode S, bishopIntervalNestLimit_decode_encode R,
        bishopIntervalNestLimit_decode_encode E, bishopIntervalNestLimit_decode_encode M,
        bishopIntervalNestLimit_decode_encode H, bishopIntervalNestLimit_decode_encode C,
        bishopIntervalNestLimit_decode_encode P, bishopIntervalNestLimit_decode_encode N]

private theorem bishopIntervalNestLimitToEventFlow_injective
    {x y : BishopIntervalNestLimitUp} :
    bishopIntervalNestLimitToEventFlow x = bishopIntervalNestLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalNestLimitFromEventFlow (bishopIntervalNestLimitToEventFlow x) =
        bishopIntervalNestLimitFromEventFlow (bishopIntervalNestLimitToEventFlow y) :=
    congrArg bishopIntervalNestLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopIntervalNestLimit_round_trip x).symm
      (Eq.trans hread (bishopIntervalNestLimit_round_trip y)))

private theorem bishopIntervalNestLimit_fields_faithful :
    ∀ x y : BishopIntervalNestLimitUp,
      bishopIntervalNestLimitFields x = bishopIntervalNestLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 D1 S1 R1 E1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 D2 S2 R2 E2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopIntervalNestLimitBHistCarrier : BHistCarrier BishopIntervalNestLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalNestLimitToEventFlow
  fromEventFlow := bishopIntervalNestLimitFromEventFlow

instance bishopIntervalNestLimitChapterTasteGate :
    ChapterTasteGate BishopIntervalNestLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopIntervalNestLimitFromEventFlow (bishopIntervalNestLimitToEventFlow x) =
      some x
    exact bishopIntervalNestLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopIntervalNestLimitToEventFlow_injective heq)

instance bishopIntervalNestLimitFieldFaithful :
    FieldFaithful BishopIntervalNestLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopIntervalNestLimitFields
  field_faithful := bishopIntervalNestLimit_fields_faithful

instance bishopIntervalNestLimitNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopIntervalNestLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopIntervalNestLimitUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopIntervalNestLimitUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopIntervalNestLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopIntervalNestLimitChapterTasteGate

theorem BishopIntervalNestLimitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopIntervalNestLimitUp) ∧
      Nonempty (FieldFaithful BishopIntervalNestLimitUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopIntervalNestLimitUp) ∧
          (∀ h : BHist, bishopIntervalNestLimitDecodeBHist
            (bishopIntervalNestLimitEncodeBHist h) = h) ∧
            (∀ x : BishopIntervalNestLimitUp,
              bishopIntervalNestLimitFromEventFlow
                (bishopIntervalNestLimitToEventFlow x) = some x) ∧
              (∀ x y : BishopIntervalNestLimitUp,
                bishopIntervalNestLimitToEventFlow x =
                  bishopIntervalNestLimitToEventFlow y → x = y) ∧
                bishopIntervalNestLimitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨bishopIntervalNestLimitChapterTasteGate⟩,
      ⟨bishopIntervalNestLimitFieldFaithful⟩,
      ⟨bishopIntervalNestLimitNontrivial⟩,
      bishopIntervalNestLimit_decode_encode,
      bishopIntervalNestLimit_round_trip,
      (fun _ _ heq => bishopIntervalNestLimitToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopIntervalNestLimitUp
