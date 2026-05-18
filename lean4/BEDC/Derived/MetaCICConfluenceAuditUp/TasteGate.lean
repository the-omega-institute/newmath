import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConfluenceAuditUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConfluenceAuditUp : Type where
  | mk (N A S D C H R P M : BHist) : MetaCICConfluenceAuditUp
  deriving DecidableEq

def metaCICConfluenceAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConfluenceAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConfluenceAuditEncodeBHist h

def metaCICConfluenceAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConfluenceAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConfluenceAuditDecodeBHist tail)

private theorem metaCICConfluenceAuditDecode_encode_bhist :
    ∀ h : BHist,
      metaCICConfluenceAuditDecodeBHist
        (metaCICConfluenceAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICConfluenceAuditFields :
    MetaCICConfluenceAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceAuditUp.mk N A S D C H R P M => [N, A, S, D, C, H, R, P, M]

def metaCICConfluenceAuditToEventFlow :
    MetaCICConfluenceAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceAuditUp.mk N A S D C H R P M =>
      [[BMark.b0],
        metaCICConfluenceAuditEncodeBHist N,
        [BMark.b1, BMark.b0],
        metaCICConfluenceAuditEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICConfluenceAuditEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICConfluenceAuditEncodeBHist M]

def metaCICConfluenceAuditFromEventFlow :
    EventFlow → Option MetaCICConfluenceAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | N :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
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
                                                      | R :: rest13 =>
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
                                                                      | M :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetaCICConfluenceAuditUp.mk
                                                                                  (metaCICConfluenceAuditDecodeBHist N)
                                                                                  (metaCICConfluenceAuditDecodeBHist A)
                                                                                  (metaCICConfluenceAuditDecodeBHist S)
                                                                                  (metaCICConfluenceAuditDecodeBHist D)
                                                                                  (metaCICConfluenceAuditDecodeBHist C)
                                                                                  (metaCICConfluenceAuditDecodeBHist H)
                                                                                  (metaCICConfluenceAuditDecodeBHist R)
                                                                                  (metaCICConfluenceAuditDecodeBHist P)
                                                                                  (metaCICConfluenceAuditDecodeBHist M))
                                                                          | _ :: _ => none

private theorem metaCICConfluenceAudit_round_trip :
    ∀ x : MetaCICConfluenceAuditUp,
      metaCICConfluenceAuditFromEventFlow
        (metaCICConfluenceAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N A S D C H R P M =>
      change
        some
          (MetaCICConfluenceAuditUp.mk
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist N))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist A))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist S))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist D))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist C))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist H))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist R))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist P))
            (metaCICConfluenceAuditDecodeBHist (metaCICConfluenceAuditEncodeBHist M))) =
          some (MetaCICConfluenceAuditUp.mk N A S D C H R P M)
      rw [metaCICConfluenceAuditDecode_encode_bhist N,
        metaCICConfluenceAuditDecode_encode_bhist A,
        metaCICConfluenceAuditDecode_encode_bhist S,
        metaCICConfluenceAuditDecode_encode_bhist D,
        metaCICConfluenceAuditDecode_encode_bhist C,
        metaCICConfluenceAuditDecode_encode_bhist H,
        metaCICConfluenceAuditDecode_encode_bhist R,
        metaCICConfluenceAuditDecode_encode_bhist P,
        metaCICConfluenceAuditDecode_encode_bhist M]

private theorem metaCICConfluenceAuditToEventFlow_injective
    {x y : MetaCICConfluenceAuditUp} :
    metaCICConfluenceAuditToEventFlow x =
      metaCICConfluenceAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConfluenceAuditFromEventFlow (metaCICConfluenceAuditToEventFlow x) =
        metaCICConfluenceAuditFromEventFlow (metaCICConfluenceAuditToEventFlow y) :=
    congrArg metaCICConfluenceAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICConfluenceAudit_round_trip x).symm
      (Eq.trans hread (metaCICConfluenceAudit_round_trip y)))

private theorem metaCICConfluenceAudit_fields_faithful :
    ∀ x y : MetaCICConfluenceAuditUp,
      metaCICConfluenceAuditFields x = metaCICConfluenceAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk N A S D C H R P M =>
      cases y with
      | mk N' A' S' D' C' H' R' P' M' =>
          cases hfields
          rfl

instance metaCICConfluenceAuditBHistCarrier :
    BHistCarrier MetaCICConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConfluenceAuditToEventFlow
  fromEventFlow := metaCICConfluenceAuditFromEventFlow

instance metaCICConfluenceAuditChapterTasteGate :
    ChapterTasteGate MetaCICConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICConfluenceAuditFromEventFlow
        (metaCICConfluenceAuditToEventFlow x) = some x
    exact metaCICConfluenceAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICConfluenceAuditToEventFlow_injective heq)

instance metaCICConfluenceAuditFieldFaithful :
    FieldFaithful MetaCICConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICConfluenceAuditFields
  field_faithful := metaCICConfluenceAudit_fields_faithful

instance metaCICConfluenceAuditNontrivial :
    Nontrivial MetaCICConfluenceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICConfluenceAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICConfluenceAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICConfluenceAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConfluenceAuditChapterTasteGate

def taste_gate_witness : FieldFaithful MetaCICConfluenceAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConfluenceAuditFieldFaithful

theorem MetaCICConfluenceAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metaCICConfluenceAuditDecodeBHist
          (metaCICConfluenceAuditEncodeBHist h) = h) ∧
      (∀ x : MetaCICConfluenceAuditUp,
        metaCICConfluenceAuditFromEventFlow
          (metaCICConfluenceAuditToEventFlow x) = some x) ∧
      (∀ x y : MetaCICConfluenceAuditUp,
        metaCICConfluenceAuditToEventFlow x =
          metaCICConfluenceAuditToEventFlow y → x = y) ∧
      metaCICConfluenceAuditEncodeBHist BHist.Empty = ([] : List BMark) ∧
      Nonempty (ChapterTasteGate MetaCICConfluenceAuditUp) ∧
      Nonempty (FieldFaithful MetaCICConfluenceAuditUp) ∧
      Nonempty (Nontrivial MetaCICConfluenceAuditUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨metaCICConfluenceAuditDecode_encode_bhist,
      metaCICConfluenceAudit_round_trip,
      fun _ _ heq => metaCICConfluenceAuditToEventFlow_injective heq,
      rfl,
      ⟨metaCICConfluenceAuditChapterTasteGate⟩,
      ⟨metaCICConfluenceAuditFieldFaithful⟩,
      ⟨metaCICConfluenceAuditNontrivial⟩⟩

end BEDC.Derived.MetaCICConfluenceAuditUp.TasteGate

namespace BEDC.Derived.MetaCICConfluenceAuditUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.MetaCICConfluenceAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.MetaCICConfluenceAuditUp
