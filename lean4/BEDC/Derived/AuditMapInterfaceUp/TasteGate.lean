import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapInterfaceUp : Type where
  | mk :
      (established conditional obstruction frontier crossMap transport route provenance
        localCert : BHist) →
      AuditMapInterfaceUp
  deriving DecidableEq

def auditMapInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapInterfaceEncodeBHist h

def auditMapInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapInterfaceDecodeBHist tail)

theorem AuditMapInterfaceUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist, auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditMapInterfaceFields : AuditMapInterfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapInterfaceUp.mk established conditional obstruction frontier crossMap transport route
      provenance localCert =>
      [established, conditional, obstruction, frontier, crossMap, transport, route, provenance,
        localCert]

def auditMapInterfaceToEventFlow : AuditMapInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map auditMapInterfaceEncodeBHist (auditMapInterfaceFields x)

private def AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault index rest

def auditMapInterfaceFromEventFlow : EventFlow → Option AuditMapInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AuditMapInterfaceUp.mk
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 0 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 1 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 2 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 3 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 4 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 5 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 6 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 7 ef))
        (auditMapInterfaceDecodeBHist
          (AuditMapInterfaceUp_single_carrier_alignment_eventAtDefault 8 ef)))

theorem AuditMapInterfaceUp_single_carrier_alignment_round_trip :
    ∀ x : AuditMapInterfaceUp,
      auditMapInterfaceFromEventFlow (auditMapInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk established conditional obstruction frontier crossMap transport route provenance
      localCert =>
      change
        some
          (AuditMapInterfaceUp.mk
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist established))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist conditional))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist obstruction))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist frontier))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist crossMap))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist transport))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist route))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist provenance))
            (auditMapInterfaceDecodeBHist (auditMapInterfaceEncodeBHist localCert))) =
          some
            (AuditMapInterfaceUp.mk established conditional obstruction frontier crossMap transport
              route provenance localCert)
      rw [AuditMapInterfaceUp_single_carrier_alignment_decode_encode established,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode conditional,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode obstruction,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode frontier,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode crossMap,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode transport,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode route,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode provenance,
        AuditMapInterfaceUp_single_carrier_alignment_decode_encode localCert]

theorem AuditMapInterfaceUp_single_carrier_alignment_toEventFlow_injective {x y : AuditMapInterfaceUp} :
    auditMapInterfaceToEventFlow x = auditMapInterfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapInterfaceFromEventFlow (auditMapInterfaceToEventFlow x) =
        auditMapInterfaceFromEventFlow (auditMapInterfaceToEventFlow y) :=
    congrArg auditMapInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AuditMapInterfaceUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AuditMapInterfaceUp_single_carrier_alignment_round_trip y)))

private theorem auditMapInterface_field_faithful :
    ∀ x y : AuditMapInterfaceUp, auditMapInterfaceFields x = auditMapInterfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk established₁ conditional₁ obstruction₁ frontier₁ crossMap₁ transport₁ route₁ provenance₁
      localCert₁ =>
      cases y with
      | mk established₂ conditional₂ obstruction₂ frontier₂ crossMap₂ transport₂ route₂ provenance₂
          localCert₂ =>
          cases h
          rfl

instance auditMapInterfaceBHistCarrier : BHistCarrier AuditMapInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapInterfaceToEventFlow
  fromEventFlow := auditMapInterfaceFromEventFlow

instance auditMapInterfaceChapterTasteGate : ChapterTasteGate AuditMapInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapInterfaceFromEventFlow (auditMapInterfaceToEventFlow x) = some x
    exact AuditMapInterfaceUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AuditMapInterfaceUp_single_carrier_alignment_toEventFlow_injective heq)

instance auditMapInterfaceFieldFaithful : FieldFaithful AuditMapInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapInterfaceFields
  field_faithful := auditMapInterface_field_faithful

instance auditMapInterfaceNontrivial : Nontrivial AuditMapInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditMapInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditMapInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapInterfaceChapterTasteGate

theorem AuditMapInterfaceUp_single_carrier_alignment :
    (∀ x : AuditMapInterfaceUp,
      auditMapInterfaceFromEventFlow (auditMapInterfaceToEventFlow x) = some x) ∧
      (∀ x y : AuditMapInterfaceUp,
        auditMapInterfaceToEventFlow x = auditMapInterfaceToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact AuditMapInterfaceUp_single_carrier_alignment_round_trip
  · intro x y heq
    exact AuditMapInterfaceUp_single_carrier_alignment_toEventFlow_injective heq

end BEDC.Derived.AuditMapInterfaceUp
