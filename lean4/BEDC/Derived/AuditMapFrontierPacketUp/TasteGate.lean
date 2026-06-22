import BEDC.Derived.AuditMapFrontierPacketUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapFrontierPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapFrontierPacketUp : Type where
  | mk (T C O R X P H Q N : BHist) : AuditMapFrontierPacketUp
  deriving DecidableEq

def auditMapFrontierPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapFrontierPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapFrontierPacketEncodeBHist h

def auditMapFrontierPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapFrontierPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapFrontierPacketDecodeBHist tail)

private theorem auditMapFrontierPacketDecodeEncode :
    ∀ h : BHist, auditMapFrontierPacketDecodeBHist
      (auditMapFrontierPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditMapFrontierPacketFields : AuditMapFrontierPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFrontierPacketUp.mk T C O R X P H Q N => [T, C, O, R, X, P, H, Q, N]

def auditMapFrontierPacketToEventFlow : AuditMapFrontierPacketUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (auditMapFrontierPacketFields x).map auditMapFrontierPacketEncodeBHist

private def auditMapFrontierPacketEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => auditMapFrontierPacketEventAtDefault index rest

def auditMapFrontierPacketFromEventFlow
    (ef : EventFlow) : Option AuditMapFrontierPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AuditMapFrontierPacketUp.mk
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 0 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 1 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 2 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 3 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 4 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 5 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 6 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 7 ef))
      (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEventAtDefault 8 ef)))

private theorem auditMapFrontierPacket_round_trip :
    ∀ x : AuditMapFrontierPacketUp,
      auditMapFrontierPacketFromEventFlow (auditMapFrontierPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T C O R X P H Q N =>
      change
        some
          (AuditMapFrontierPacketUp.mk
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist T))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist C))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist O))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist R))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist X))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist P))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist H))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist Q))
            (auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist N))) =
          some (AuditMapFrontierPacketUp.mk T C O R X P H Q N)
      rw [auditMapFrontierPacketDecodeEncode T, auditMapFrontierPacketDecodeEncode C,
        auditMapFrontierPacketDecodeEncode O, auditMapFrontierPacketDecodeEncode R,
        auditMapFrontierPacketDecodeEncode X, auditMapFrontierPacketDecodeEncode P,
        auditMapFrontierPacketDecodeEncode H, auditMapFrontierPacketDecodeEncode Q,
        auditMapFrontierPacketDecodeEncode N]

private theorem auditMapFrontierPacketToEventFlow_injective {x y : AuditMapFrontierPacketUp} :
    auditMapFrontierPacketToEventFlow x = auditMapFrontierPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapFrontierPacketFromEventFlow (auditMapFrontierPacketToEventFlow x) =
        auditMapFrontierPacketFromEventFlow (auditMapFrontierPacketToEventFlow y) :=
    congrArg auditMapFrontierPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapFrontierPacket_round_trip x).symm
      (Eq.trans hread (auditMapFrontierPacket_round_trip y)))

private theorem auditMapFrontierPacketFieldFaithfulProof :
    ∀ x y : AuditMapFrontierPacketUp,
      auditMapFrontierPacketFields x = auditMapFrontierPacketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T₁ C₁ O₁ R₁ X₁ P₁ H₁ Q₁ N₁ =>
      cases y with
      | mk T₂ C₂ O₂ R₂ X₂ P₂ H₂ Q₂ N₂ =>
          change [T₁, C₁, O₁, R₁, X₁, P₁, H₁, Q₁, N₁] =
            [T₂, C₂, O₂, R₂, X₂, P₂, H₂, Q₂, N₂] at h
          cases h
          rfl

instance auditMapFrontierPacketBHistCarrier :
    BHistCarrier AuditMapFrontierPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapFrontierPacketToEventFlow
  fromEventFlow := auditMapFrontierPacketFromEventFlow

instance auditMapFrontierPacketChapterTasteGate :
    ChapterTasteGate AuditMapFrontierPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapFrontierPacketFromEventFlow
      (auditMapFrontierPacketToEventFlow x) = some x
    exact auditMapFrontierPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapFrontierPacketToEventFlow_injective heq)

instance auditMapFrontierPacketFieldFaithful :
    FieldFaithful AuditMapFrontierPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapFrontierPacketFields
  field_faithful := auditMapFrontierPacketFieldFaithfulProof

instance auditMapFrontierPacketNontrivial :
    Nontrivial AuditMapFrontierPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapFrontierPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditMapFrontierPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AuditMapFrontierPacketTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AuditMapFrontierPacketUp) ∧
      Nonempty (FieldFaithful AuditMapFrontierPacketUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AuditMapFrontierPacketUp) ∧
          (∀ h : BHist,
            auditMapFrontierPacketDecodeBHist (auditMapFrontierPacketEncodeBHist h) = h) ∧
            (∀ x : AuditMapFrontierPacketUp,
              auditMapFrontierPacketFromEventFlow
                (auditMapFrontierPacketToEventFlow x) = some x) ∧
              (∀ x y : AuditMapFrontierPacketUp,
                auditMapFrontierPacketToEventFlow x =
                  auditMapFrontierPacketToEventFlow y → x = y) ∧
                auditMapFrontierPacketEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨auditMapFrontierPacketChapterTasteGate⟩,
      ⟨auditMapFrontierPacketFieldFaithful⟩,
      ⟨auditMapFrontierPacketNontrivial⟩,
      auditMapFrontierPacketDecodeEncode,
      auditMapFrontierPacket_round_trip,
      by
        intro x y heq
        exact auditMapFrontierPacketToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.AuditMapFrontierPacketUp
