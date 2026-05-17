import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditSystemUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditSystemUp : Type where
  | mk : (C P F R E L H K Q N : BHist) → AuditSystemUp
  deriving DecidableEq

def auditSystemEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditSystemEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditSystemEncodeBHist h

def auditSystemDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditSystemDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditSystemDecodeBHist tail)

private theorem auditSystemDecode_encode_bhist :
    ∀ h : BHist, auditSystemDecodeBHist (auditSystemEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditSystemToEventFlow : AuditSystemUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditSystemUp.mk C P F R E L H K Q N =>
      [auditSystemEncodeBHist C, auditSystemEncodeBHist P, auditSystemEncodeBHist F,
        auditSystemEncodeBHist R, auditSystemEncodeBHist E, auditSystemEncodeBHist L,
        auditSystemEncodeBHist H, auditSystemEncodeBHist K, auditSystemEncodeBHist Q,
        auditSystemEncodeBHist N]

def auditSystemFromEventFlow : EventFlow → Option AuditSystemUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | C :: rest0 =>
      match rest0 with
      | [] => none
      | P :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | K :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | Q :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (AuditSystemUp.mk
                                                  (auditSystemDecodeBHist C)
                                                  (auditSystemDecodeBHist P)
                                                  (auditSystemDecodeBHist F)
                                                  (auditSystemDecodeBHist R)
                                                  (auditSystemDecodeBHist E)
                                                  (auditSystemDecodeBHist L)
                                                  (auditSystemDecodeBHist H)
                                                  (auditSystemDecodeBHist K)
                                                  (auditSystemDecodeBHist Q)
                                                  (auditSystemDecodeBHist N))
                                          | _ :: _ => none

private theorem auditSystem_round_trip :
    ∀ x : AuditSystemUp, auditSystemFromEventFlow (auditSystemToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C P F R E L H K Q N =>
      change
        some
            (AuditSystemUp.mk
              (auditSystemDecodeBHist (auditSystemEncodeBHist C))
              (auditSystemDecodeBHist (auditSystemEncodeBHist P))
              (auditSystemDecodeBHist (auditSystemEncodeBHist F))
              (auditSystemDecodeBHist (auditSystemEncodeBHist R))
              (auditSystemDecodeBHist (auditSystemEncodeBHist E))
              (auditSystemDecodeBHist (auditSystemEncodeBHist L))
              (auditSystemDecodeBHist (auditSystemEncodeBHist H))
              (auditSystemDecodeBHist (auditSystemEncodeBHist K))
              (auditSystemDecodeBHist (auditSystemEncodeBHist Q))
              (auditSystemDecodeBHist (auditSystemEncodeBHist N))) =
          some (AuditSystemUp.mk C P F R E L H K Q N)
      rw [auditSystemDecode_encode_bhist C, auditSystemDecode_encode_bhist P,
        auditSystemDecode_encode_bhist F, auditSystemDecode_encode_bhist R,
        auditSystemDecode_encode_bhist E, auditSystemDecode_encode_bhist L,
        auditSystemDecode_encode_bhist H, auditSystemDecode_encode_bhist K,
        auditSystemDecode_encode_bhist Q, auditSystemDecode_encode_bhist N]

private theorem auditSystemToEventFlow_injective {x y : AuditSystemUp} :
    auditSystemToEventFlow x = auditSystemToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditSystemFromEventFlow (auditSystemToEventFlow x) =
        auditSystemFromEventFlow (auditSystemToEventFlow y) :=
    congrArg auditSystemFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditSystem_round_trip x).symm
      (Eq.trans hread (auditSystem_round_trip y)))

instance auditSystemBHistCarrier : BHistCarrier AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditSystemToEventFlow
  fromEventFlow := auditSystemFromEventFlow

instance auditSystemChapterTasteGate : ChapterTasteGate AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditSystemFromEventFlow (auditSystemToEventFlow x) = some x
    exact auditSystem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditSystemToEventFlow_injective heq)

instance auditSystemFieldFaithful : FieldFaithful AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AuditSystemUp.mk C P F R E L H K Q N => [C, P, F, R, E, L, H, K, Q, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk C1 P1 F1 R1 E1 L1 H1 K1 Q1 N1 =>
        cases y with
        | mk C2 P2 F2 R2 E2 L2 H2 K2 Q2 N2 =>
            cases h
            rfl

instance auditSystemNontrivial : Nontrivial AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditSystemUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditSystemUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditSystemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditSystemChapterTasteGate

theorem AuditSystemTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditSystemDecodeBHist (auditSystemEncodeBHist h) = h) ∧
      (∀ x : AuditSystemUp, auditSystemFromEventFlow (auditSystemToEventFlow x) = some x) ∧
        (∀ x y : AuditSystemUp,
          auditSystemToEventFlow x = auditSystemToEventFlow y → x = y) ∧
          auditSystemEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditSystemDecode_encode_bhist
  · constructor
    · intro x
      change auditSystemFromEventFlow (auditSystemToEventFlow x) = some x
      exact auditSystem_round_trip x
    · constructor
      · intro x y heq
        exact auditSystemToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditSystemUp
