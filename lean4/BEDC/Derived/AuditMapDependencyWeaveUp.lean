import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapDependencyWeaveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapDependencyWeaveUp : Type where
  | mk (M L O F S H C P N : BHist) : AuditMapDependencyWeaveUp
  deriving DecidableEq

def auditMapDependencyWeaveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapDependencyWeaveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapDependencyWeaveEncodeBHist h

def auditMapDependencyWeaveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapDependencyWeaveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapDependencyWeaveDecodeBHist tail)

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditMapDependencyWeaveToEventFlow : AuditMapDependencyWeaveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapDependencyWeaveUp.mk M L O F S H C P N =>
      [[BMark.b0],
        auditMapDependencyWeaveEncodeBHist M,
        [BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapDependencyWeaveEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist N]

def auditMapDependencyWeaveFromEventFlow : EventFlow → Option AuditMapDependencyWeaveUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagM :: restM =>
      match restM with
      | [] => none
      | M :: restLTag =>
          match restLTag with
          | [] => none
          | _tagL :: restL =>
              match restL with
              | [] => none
              | L :: restOTag =>
                  match restOTag with
                  | [] => none
                  | _tagO :: restO =>
                      match restO with
                      | [] => none
                      | O :: restFTag =>
                          match restFTag with
                          | [] => none
                          | _tagF :: restF =>
                              match restF with
                              | [] => none
                              | F :: restSTag =>
                                  match restSTag with
                                  | [] => none
                                  | _tagS :: restS =>
                                      match restS with
                                      | [] => none
                                      | S :: restHTag =>
                                          match restHTag with
                                          | [] => none
                                          | _tagH :: restH =>
                                              match restH with
                                              | [] => none
                                              | H :: restCTag =>
                                                  match restCTag with
                                                  | [] => none
                                                  | _tagC :: restC =>
                                                      match restC with
                                                      | [] => none
                                                      | C :: restPTag =>
                                                          match restPTag with
                                                          | [] => none
                                                          | _tagP :: restP =>
                                                              match restP with
                                                              | [] => none
                                                              | P :: restNTag =>
                                                                  match restNTag with
                                                                  | [] => none
                                                                  | _tagN :: restN =>
                                                                      match restN with
                                                                      | [] => none
                                                                      | N :: rest =>
                                                                          match rest with
                                                                          | [] =>
                                                                              some
                                                                                (AuditMapDependencyWeaveUp.mk
                                                                                  (auditMapDependencyWeaveDecodeBHist M)
                                                                                  (auditMapDependencyWeaveDecodeBHist L)
                                                                                  (auditMapDependencyWeaveDecodeBHist O)
                                                                                  (auditMapDependencyWeaveDecodeBHist F)
                                                                                  (auditMapDependencyWeaveDecodeBHist S)
                                                                                  (auditMapDependencyWeaveDecodeBHist H)
                                                                                  (auditMapDependencyWeaveDecodeBHist C)
                                                                                  (auditMapDependencyWeaveDecodeBHist P)
                                                                                  (auditMapDependencyWeaveDecodeBHist N))
                                                                          | _ :: _ => none

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AuditMapDependencyWeaveUp,
      auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M L O F S H C P N =>
      change
        some
          (AuditMapDependencyWeaveUp.mk
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist M))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist L))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist O))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist F))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist S))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist H))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist C))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist P))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist N))) =
          some (AuditMapDependencyWeaveUp.mk M L O F S H C P N)
      rw [AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode M,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode L,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode O,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode F,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode S,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode H,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode C,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode P,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode N]

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_injective
    {x y : AuditMapDependencyWeaveUp} :
    auditMapDependencyWeaveToEventFlow x = auditMapDependencyWeaveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) =
        auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow y) :=
    congrArg auditMapDependencyWeaveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip y)))

private def auditMapDependencyWeaveFields : AuditMapDependencyWeaveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapDependencyWeaveUp.mk M L O F S H C P N => [M, L, O, F, S, H, C, P, N]

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_fields :
    ∀ x y : AuditMapDependencyWeaveUp,
      auditMapDependencyWeaveFields x = auditMapDependencyWeaveFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 L1 O1 F1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 L2 O2 F2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance auditMapDependencyWeaveBHistCarrier :
    BHistCarrier AuditMapDependencyWeaveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapDependencyWeaveToEventFlow
  fromEventFlow := auditMapDependencyWeaveFromEventFlow

instance auditMapDependencyWeaveChapterTasteGate :
    ChapterTasteGate AuditMapDependencyWeaveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) = some x
    exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AuditMapDependencyWeaveTasteGate_single_carrier_alignment_injective heq)

instance auditMapDependencyWeaveFieldFaithful :
    FieldFaithful AuditMapDependencyWeaveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapDependencyWeaveFields
  field_faithful := AuditMapDependencyWeaveTasteGate_single_carrier_alignment_fields

theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist h) = h) ∧
      (∀ x : AuditMapDependencyWeaveUp,
        auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) = some x) ∧
        (∀ x y : AuditMapDependencyWeaveUp,
          auditMapDependencyWeaveToEventFlow x = auditMapDependencyWeaveToEventFlow y → x = y) ∧
          auditMapDependencyWeaveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode
  constructor
  · exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.AuditMapDependencyWeaveUp
