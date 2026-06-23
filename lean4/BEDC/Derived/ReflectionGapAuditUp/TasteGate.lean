import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReflectionGapAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReflectionGapAuditUp : Type where
  | mk (I G L Q F T R P N : BHist) : ReflectionGapAuditUp
  deriving DecidableEq

def reflectionGapAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reflectionGapAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reflectionGapAuditEncodeBHist h

def reflectionGapAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reflectionGapAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reflectionGapAuditDecodeBHist tail)

private theorem reflectionGapAuditDecode_encode_bhist :
    ∀ h : BHist, reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def reflectionGapAuditFields : ReflectionGapAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectionGapAuditUp.mk I G L Q F T R P N => [I, G, L, Q, F, T, R, P, N]

def reflectionGapAuditToEventFlow : ReflectionGapAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (reflectionGapAuditFields x).map reflectionGapAuditEncodeBHist

def reflectionGapAuditFromEventFlow : EventFlow → Option ReflectionGapAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | G :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ReflectionGapAuditUp.mk
                                              (reflectionGapAuditDecodeBHist I)
                                              (reflectionGapAuditDecodeBHist G)
                                              (reflectionGapAuditDecodeBHist L)
                                              (reflectionGapAuditDecodeBHist Q)
                                              (reflectionGapAuditDecodeBHist F)
                                              (reflectionGapAuditDecodeBHist T)
                                              (reflectionGapAuditDecodeBHist R)
                                              (reflectionGapAuditDecodeBHist P)
                                              (reflectionGapAuditDecodeBHist N))
                                      | _ :: _ => none

private theorem reflectionGapAudit_round_trip :
    ∀ x : ReflectionGapAuditUp,
      reflectionGapAuditFromEventFlow (reflectionGapAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I G L Q F T R P N =>
      change
        some
          (ReflectionGapAuditUp.mk
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist I))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist G))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist L))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist Q))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist F))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist T))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist R))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist P))
            (reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist N))) =
          some (ReflectionGapAuditUp.mk I G L Q F T R P N)
      rw [reflectionGapAuditDecode_encode_bhist I, reflectionGapAuditDecode_encode_bhist G,
        reflectionGapAuditDecode_encode_bhist L, reflectionGapAuditDecode_encode_bhist Q,
        reflectionGapAuditDecode_encode_bhist F, reflectionGapAuditDecode_encode_bhist T,
        reflectionGapAuditDecode_encode_bhist R, reflectionGapAuditDecode_encode_bhist P,
        reflectionGapAuditDecode_encode_bhist N]

private theorem reflectionGapAuditToEventFlow_injective {x y : ReflectionGapAuditUp} :
    reflectionGapAuditToEventFlow x = reflectionGapAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reflectionGapAuditFromEventFlow (reflectionGapAuditToEventFlow x) =
        reflectionGapAuditFromEventFlow (reflectionGapAuditToEventFlow y) :=
    congrArg reflectionGapAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reflectionGapAudit_round_trip x).symm
      (Eq.trans hread (reflectionGapAudit_round_trip y)))

private theorem reflectionGapAudit_fields_faithful :
    ∀ x y : ReflectionGapAuditUp, reflectionGapAuditFields x = reflectionGapAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 G1 L1 Q1 F1 T1 R1 P1 N1 =>
      cases y with
      | mk I2 G2 L2 Q2 F2 T2 R2 P2 N2 =>
          cases hfields
          rfl

instance reflectionGapAuditBHistCarrier : BHistCarrier ReflectionGapAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reflectionGapAuditToEventFlow
  fromEventFlow := reflectionGapAuditFromEventFlow

instance reflectionGapAuditChapterTasteGate : ChapterTasteGate ReflectionGapAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reflectionGapAuditFromEventFlow (reflectionGapAuditToEventFlow x) = some x
    exact reflectionGapAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reflectionGapAuditToEventFlow_injective heq)

instance reflectionGapAuditFieldFaithful : FieldFaithful ReflectionGapAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reflectionGapAuditFields
  field_faithful := reflectionGapAudit_fields_faithful

instance reflectionGapAuditNontrivial : Nontrivial ReflectionGapAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReflectionGapAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ReflectionGapAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ReflectionGapAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  reflectionGapAuditChapterTasteGate

namespace TasteGate

theorem ReflectionGapAuditTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ReflectionGapAuditUp) ∧
      Nonempty (FieldFaithful ReflectionGapAuditUp) ∧
        Nonempty (Nontrivial ReflectionGapAuditUp) ∧
          (∀ h : BHist, reflectionGapAuditDecodeBHist (reflectionGapAuditEncodeBHist h) = h) ∧
            (∀ x : ReflectionGapAuditUp,
              reflectionGapAuditFromEventFlow (reflectionGapAuditToEventFlow x) = some x) ∧
              (∀ x y : ReflectionGapAuditUp,
                reflectionGapAuditToEventFlow x = reflectionGapAuditToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨reflectionGapAuditChapterTasteGate⟩
  · constructor
    · exact ⟨reflectionGapAuditFieldFaithful⟩
    · constructor
      · exact ⟨reflectionGapAuditNontrivial⟩
      · constructor
        · exact reflectionGapAuditDecode_encode_bhist
        · constructor
          · exact reflectionGapAudit_round_trip
          · intro x y heq
            exact reflectionGapAuditToEventFlow_injective heq

def taste_gate : ChapterTasteGate ReflectionGapAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.ReflectionGapAuditUp.taste_gate

end TasteGate

end BEDC.Derived.ReflectionGapAuditUp
