import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelContextAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelContextAuditUp : Type where
  | mk : (C T M A V R H K P N : BHist) → LargeModelContextAuditUp
  deriving DecidableEq

def largeModelContextAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelContextAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelContextAuditEncodeBHist h

def largeModelContextAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelContextAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelContextAuditDecodeBHist tail)

private theorem largeModelContextAuditDecode_encode_bhist :
    ∀ h : BHist,
      largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def largeModelContextAuditToEventFlow : LargeModelContextAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelContextAuditUp.mk C T M A V R H K P N =>
      [[BMark.b0],
        largeModelContextAuditEncodeBHist C,
        [BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        largeModelContextAuditEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        largeModelContextAuditEncodeBHist N]

def largeModelContextAuditFromEventFlow : EventFlow → Option LargeModelContextAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
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
                      | M :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | A :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | V :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | K :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (LargeModelContextAuditUp.mk
                                                                                          (largeModelContextAuditDecodeBHist C)
                                                                                          (largeModelContextAuditDecodeBHist T)
                                                                                          (largeModelContextAuditDecodeBHist M)
                                                                                          (largeModelContextAuditDecodeBHist A)
                                                                                          (largeModelContextAuditDecodeBHist V)
                                                                                          (largeModelContextAuditDecodeBHist R)
                                                                                          (largeModelContextAuditDecodeBHist H)
                                                                                          (largeModelContextAuditDecodeBHist K)
                                                                                          (largeModelContextAuditDecodeBHist P)
                                                                                          (largeModelContextAuditDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem largeModelContextAudit_round_trip :
    ∀ x : LargeModelContextAuditUp,
      largeModelContextAuditFromEventFlow (largeModelContextAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C T M A V R H K P N =>
      change
        some
          (LargeModelContextAuditUp.mk
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist C))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist T))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist M))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist A))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist V))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist R))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist H))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist K))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist P))
            (largeModelContextAuditDecodeBHist (largeModelContextAuditEncodeBHist N))) =
          some (LargeModelContextAuditUp.mk C T M A V R H K P N)
      rw [largeModelContextAuditDecode_encode_bhist C,
        largeModelContextAuditDecode_encode_bhist T,
        largeModelContextAuditDecode_encode_bhist M,
        largeModelContextAuditDecode_encode_bhist A,
        largeModelContextAuditDecode_encode_bhist V,
        largeModelContextAuditDecode_encode_bhist R,
        largeModelContextAuditDecode_encode_bhist H,
        largeModelContextAuditDecode_encode_bhist K,
        largeModelContextAuditDecode_encode_bhist P,
        largeModelContextAuditDecode_encode_bhist N]

private theorem largeModelContextAuditToEventFlow_injective {x y : LargeModelContextAuditUp} :
    largeModelContextAuditToEventFlow x = largeModelContextAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelContextAuditFromEventFlow (largeModelContextAuditToEventFlow x) =
        largeModelContextAuditFromEventFlow (largeModelContextAuditToEventFlow y) :=
    congrArg largeModelContextAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelContextAudit_round_trip x).symm
      (Eq.trans hread (largeModelContextAudit_round_trip y)))

instance largeModelContextAuditBHistCarrier : BHistCarrier LargeModelContextAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelContextAuditToEventFlow
  fromEventFlow := largeModelContextAuditFromEventFlow

instance largeModelContextAuditChapterTasteGate : ChapterTasteGate LargeModelContextAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelContextAuditFromEventFlow (largeModelContextAuditToEventFlow x) = some x
    exact largeModelContextAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelContextAuditToEventFlow_injective heq)

instance largeModelContextAuditFieldFaithful : FieldFaithful LargeModelContextAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LargeModelContextAuditUp.mk C T M A V R H K P N => [C, T, M, A, V, R, H, K, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk C1 T1 M1 A1 V1 R1 H1 K1 P1 N1 =>
        cases y with
        | mk C2 T2 M2 A2 V2 R2 H2 K2 P2 N2 =>
            cases h
            rfl

instance largeModelContextAuditNontrivial : Nontrivial LargeModelContextAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelContextAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelContextAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LargeModelContextAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelContextAuditChapterTasteGate

theorem LargeModelContextAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, largeModelContextAuditDecodeBHist
        (largeModelContextAuditEncodeBHist h) = h) ∧
      (∀ x : LargeModelContextAuditUp,
        largeModelContextAuditFromEventFlow (largeModelContextAuditToEventFlow x) = some x) ∧
      (∀ x y : LargeModelContextAuditUp,
        largeModelContextAuditToEventFlow x = largeModelContextAuditToEventFlow y → x = y) ∧
      largeModelContextAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact largeModelContextAuditDecode_encode_bhist h
  · constructor
    · intro x
      exact largeModelContextAudit_round_trip x
    · constructor
      · intro x y heq
        exact largeModelContextAuditToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelContextAuditUp

namespace BEDC.Derived.LargeModelContextAuditUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived.LargeModelContextAuditUp

theorem LargeModelContextAuditTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LargeModelContextAuditUp) ∧
      Nonempty (ChapterTasteGate LargeModelContextAuditUp) ∧
        Nonempty (FieldFaithful LargeModelContextAuditUp) ∧
          Nonempty (Nontrivial LargeModelContextAuditUp) ∧
            largeModelContextAuditEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              largeModelContextAuditEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨largeModelContextAuditBHistCarrier⟩
  · constructor
    · exact ⟨largeModelContextAuditChapterTasteGate⟩
    · constructor
      · exact ⟨largeModelContextAuditFieldFaithful⟩
      · constructor
        · exact ⟨largeModelContextAuditNontrivial⟩
        · constructor
          · rfl
          · rfl

end BEDC.Derived.LargeModelContextAuditUp.TasteGate
