import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineInterfaceFormalizationTargetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineInterfaceFormalizationTargetUp : Type where
  | mk
      (targetName namespaceRow registry statementSkeleton dependencyList expectedStatus
        auditGate notClaimed transport continuation provenance localName : BHist) :
      MachineInterfaceFormalizationTargetUp
  deriving DecidableEq

def machineInterfaceFormalizationTargetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: machineInterfaceFormalizationTargetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: machineInterfaceFormalizationTargetEncodeBHist h

def machineInterfaceFormalizationTargetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (machineInterfaceFormalizationTargetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (machineInterfaceFormalizationTargetDecodeBHist tail)

private theorem machineInterfaceFormalizationTargetDecode_encode_bhist :
    ∀ h : BHist,
      machineInterfaceFormalizationTargetDecodeBHist
        (machineInterfaceFormalizationTargetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def machineInterfaceFormalizationTargetDecodePacket
    (targetName namespaceRow registry statementSkeleton dependencyList expectedStatus auditGate
      notClaimed transport continuation provenance localName : RawEvent) :
    MachineInterfaceFormalizationTargetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  MachineInterfaceFormalizationTargetUp.mk
    (machineInterfaceFormalizationTargetDecodeBHist targetName)
    (machineInterfaceFormalizationTargetDecodeBHist namespaceRow)
    (machineInterfaceFormalizationTargetDecodeBHist registry)
    (machineInterfaceFormalizationTargetDecodeBHist statementSkeleton)
    (machineInterfaceFormalizationTargetDecodeBHist dependencyList)
    (machineInterfaceFormalizationTargetDecodeBHist expectedStatus)
    (machineInterfaceFormalizationTargetDecodeBHist auditGate)
    (machineInterfaceFormalizationTargetDecodeBHist notClaimed)
    (machineInterfaceFormalizationTargetDecodeBHist transport)
    (machineInterfaceFormalizationTargetDecodeBHist continuation)
    (machineInterfaceFormalizationTargetDecodeBHist provenance)
    (machineInterfaceFormalizationTargetDecodeBHist localName)

def machineInterfaceFormalizationTargetToEventFlow :
    MachineInterfaceFormalizationTargetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MachineInterfaceFormalizationTargetUp.mk targetName namespaceRow registry statementSkeleton
      dependencyList expectedStatus auditGate notClaimed transport continuation provenance
      localName =>
      [machineInterfaceFormalizationTargetEncodeBHist targetName,
        machineInterfaceFormalizationTargetEncodeBHist namespaceRow,
        machineInterfaceFormalizationTargetEncodeBHist registry,
        machineInterfaceFormalizationTargetEncodeBHist statementSkeleton,
        machineInterfaceFormalizationTargetEncodeBHist dependencyList,
        machineInterfaceFormalizationTargetEncodeBHist expectedStatus,
        machineInterfaceFormalizationTargetEncodeBHist auditGate,
        machineInterfaceFormalizationTargetEncodeBHist notClaimed,
        machineInterfaceFormalizationTargetEncodeBHist transport,
        machineInterfaceFormalizationTargetEncodeBHist continuation,
        machineInterfaceFormalizationTargetEncodeBHist provenance,
        machineInterfaceFormalizationTargetEncodeBHist localName]

def machineInterfaceFormalizationTargetFromEventFlow :
    EventFlow → Option MachineInterfaceFormalizationTargetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | targetName :: rest0 =>
      match rest0 with
      | [] => none
      | namespaceRow :: rest1 =>
          match rest1 with
          | [] => none
          | registry :: rest2 =>
              match rest2 with
              | [] => none
              | statementSkeleton :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dependencyList :: rest4 =>
                      match rest4 with
                      | [] => none
                      | expectedStatus :: rest5 =>
                          match rest5 with
                          | [] => none
                          | auditGate :: rest6 =>
                              match rest6 with
                              | [] => none
                              | notClaimed :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | continuation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localName :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (machineInterfaceFormalizationTargetDecodePacket
                                                          targetName namespaceRow registry
                                                          statementSkeleton dependencyList
                                                          expectedStatus auditGate notClaimed
                                                          transport continuation provenance
                                                          localName)
                                                  | _ :: _ => none

private theorem machineInterfaceFormalizationTarget_round_trip :
    ∀ x : MachineInterfaceFormalizationTargetUp,
      machineInterfaceFormalizationTargetFromEventFlow
        (machineInterfaceFormalizationTargetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk targetName namespaceRow registry statementSkeleton dependencyList expectedStatus auditGate
      notClaimed transport continuation provenance localName =>
      change
        some
            (machineInterfaceFormalizationTargetDecodePacket
              (machineInterfaceFormalizationTargetEncodeBHist targetName)
              (machineInterfaceFormalizationTargetEncodeBHist namespaceRow)
              (machineInterfaceFormalizationTargetEncodeBHist registry)
              (machineInterfaceFormalizationTargetEncodeBHist statementSkeleton)
              (machineInterfaceFormalizationTargetEncodeBHist dependencyList)
              (machineInterfaceFormalizationTargetEncodeBHist expectedStatus)
              (machineInterfaceFormalizationTargetEncodeBHist auditGate)
              (machineInterfaceFormalizationTargetEncodeBHist notClaimed)
              (machineInterfaceFormalizationTargetEncodeBHist transport)
              (machineInterfaceFormalizationTargetEncodeBHist continuation)
              (machineInterfaceFormalizationTargetEncodeBHist provenance)
              (machineInterfaceFormalizationTargetEncodeBHist localName)) =
          some
            (MachineInterfaceFormalizationTargetUp.mk targetName namespaceRow registry
              statementSkeleton dependencyList expectedStatus auditGate notClaimed transport
              continuation provenance localName)
      unfold machineInterfaceFormalizationTargetDecodePacket
      rw [machineInterfaceFormalizationTargetDecode_encode_bhist targetName,
        machineInterfaceFormalizationTargetDecode_encode_bhist namespaceRow,
        machineInterfaceFormalizationTargetDecode_encode_bhist registry,
        machineInterfaceFormalizationTargetDecode_encode_bhist statementSkeleton,
        machineInterfaceFormalizationTargetDecode_encode_bhist dependencyList,
        machineInterfaceFormalizationTargetDecode_encode_bhist expectedStatus,
        machineInterfaceFormalizationTargetDecode_encode_bhist auditGate,
        machineInterfaceFormalizationTargetDecode_encode_bhist notClaimed,
        machineInterfaceFormalizationTargetDecode_encode_bhist transport,
        machineInterfaceFormalizationTargetDecode_encode_bhist continuation,
        machineInterfaceFormalizationTargetDecode_encode_bhist provenance,
        machineInterfaceFormalizationTargetDecode_encode_bhist localName]

private theorem machineInterfaceFormalizationTargetToEventFlow_injective
    {x y : MachineInterfaceFormalizationTargetUp} :
    machineInterfaceFormalizationTargetToEventFlow x =
        machineInterfaceFormalizationTargetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      machineInterfaceFormalizationTargetFromEventFlow
          (machineInterfaceFormalizationTargetToEventFlow x) =
        machineInterfaceFormalizationTargetFromEventFlow
          (machineInterfaceFormalizationTargetToEventFlow y) :=
    congrArg machineInterfaceFormalizationTargetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (machineInterfaceFormalizationTarget_round_trip x).symm
      (Eq.trans hread (machineInterfaceFormalizationTarget_round_trip y)))

def machineInterfaceFormalizationTargetFields :
    MachineInterfaceFormalizationTargetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MachineInterfaceFormalizationTargetUp.mk targetName namespaceRow registry statementSkeleton
      dependencyList expectedStatus auditGate notClaimed transport continuation provenance
      localName =>
      [targetName, namespaceRow, registry, statementSkeleton, dependencyList, expectedStatus,
        auditGate, notClaimed, transport, continuation, provenance, localName]

private theorem machineInterfaceFormalizationTarget_fields_faithful :
    ∀ x y : MachineInterfaceFormalizationTargetUp,
      machineInterfaceFormalizationTargetFields x =
        machineInterfaceFormalizationTargetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk targetName₁ namespaceRow₁ registry₁ statementSkeleton₁ dependencyList₁ expectedStatus₁
      auditGate₁ notClaimed₁ transport₁ continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk targetName₂ namespaceRow₂ registry₂ statementSkeleton₂ dependencyList₂
          expectedStatus₂ auditGate₂ notClaimed₂ transport₂ continuation₂ provenance₂
          localName₂ =>
          injection hfields with hTargetName tail0
          injection tail0 with hNamespace tail1
          injection tail1 with hRegistry tail2
          injection tail2 with hStatementSkeleton tail3
          injection tail3 with hDependencyList tail4
          injection tail4 with hExpectedStatus tail5
          injection tail5 with hAuditGate tail6
          injection tail6 with hNotClaimed tail7
          injection tail7 with hTransport tail8
          injection tail8 with hContinuation tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hLocalName _
          subst hTargetName
          subst hNamespace
          subst hRegistry
          subst hStatementSkeleton
          subst hDependencyList
          subst hExpectedStatus
          subst hAuditGate
          subst hNotClaimed
          subst hTransport
          subst hContinuation
          subst hProvenance
          subst hLocalName
          rfl

instance machineInterfaceFormalizationTargetBHistCarrier :
    BHistCarrier MachineInterfaceFormalizationTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := machineInterfaceFormalizationTargetToEventFlow
  fromEventFlow := machineInterfaceFormalizationTargetFromEventFlow

instance machineInterfaceFormalizationTargetChapterTasteGate :
    ChapterTasteGate MachineInterfaceFormalizationTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      machineInterfaceFormalizationTargetFromEventFlow
        (machineInterfaceFormalizationTargetToEventFlow x) = some x
    exact machineInterfaceFormalizationTarget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineInterfaceFormalizationTargetToEventFlow_injective heq)

instance machineInterfaceFormalizationTargetFieldFaithful :
    FieldFaithful MachineInterfaceFormalizationTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := machineInterfaceFormalizationTargetFields
  field_faithful := machineInterfaceFormalizationTarget_fields_faithful

instance machineInterfaceFormalizationTargetNontrivial :
    Nontrivial MachineInterfaceFormalizationTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineInterfaceFormalizationTargetUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      MachineInterfaceFormalizationTargetUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MachineInterfaceFormalizationTargetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  machineInterfaceFormalizationTargetChapterTasteGate

theorem MachineInterfaceFormalizationTargetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      machineInterfaceFormalizationTargetDecodeBHist
        (machineInterfaceFormalizationTargetEncodeBHist h) = h) ∧
      (∀ x : MachineInterfaceFormalizationTargetUp,
        machineInterfaceFormalizationTargetFromEventFlow
          (machineInterfaceFormalizationTargetToEventFlow x) = some x) ∧
        (∀ x y : MachineInterfaceFormalizationTargetUp,
          machineInterfaceFormalizationTargetToEventFlow x =
              machineInterfaceFormalizationTargetToEventFlow y →
            x = y) ∧
          Nonempty (FieldFaithful MachineInterfaceFormalizationTargetUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial
              MachineInterfaceFormalizationTargetUp) ∧
              machineInterfaceFormalizationTargetEncodeBHist BHist.Empty =
                ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨machineInterfaceFormalizationTargetDecode_encode_bhist,
      machineInterfaceFormalizationTarget_round_trip,
      (fun _ _ heq => machineInterfaceFormalizationTargetToEventFlow_injective heq),
      ⟨machineInterfaceFormalizationTargetFieldFaithful⟩,
      ⟨machineInterfaceFormalizationTargetNontrivial⟩,
      rfl⟩

end BEDC.Derived.MachineInterfaceFormalizationTargetUp
