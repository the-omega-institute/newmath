import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineInterfaceFormalizationTargetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineInterfaceFormalizationTargetUp : Type where
  | mk :
      (targetName namespaceRow registry skeleton dependencies expectedStatus auditGate notClaimed
        transport route provenance localName : BHist) →
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

theorem machineInterfaceFormalizationTargetDecode_encode_bhist :
    ∀ h : BHist,
      machineInterfaceFormalizationTargetDecodeBHist
        (machineInterfaceFormalizationTargetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def machineInterfaceFormalizationTargetRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => machineInterfaceFormalizationTargetRawAt n rest

private theorem machineInterfaceFormalizationTarget_mk_congr
    {targetName targetName' namespaceRow namespaceRow' registry registry' skeleton skeleton'
      dependencies dependencies' expectedStatus expectedStatus' auditGate auditGate'
      notClaimed notClaimed' transport transport' route route' provenance provenance'
      localName localName' : BHist}
    (hTargetName : targetName' = targetName)
    (hNamespace : namespaceRow' = namespaceRow)
    (hRegistry : registry' = registry)
    (hSkeleton : skeleton' = skeleton)
    (hDependencies : dependencies' = dependencies)
    (hExpectedStatus : expectedStatus' = expectedStatus)
    (hAuditGate : auditGate' = auditGate)
    (hNotClaimed : notClaimed' = notClaimed)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    MachineInterfaceFormalizationTargetUp.mk targetName' namespaceRow' registry' skeleton'
        dependencies' expectedStatus' auditGate' notClaimed' transport' route' provenance'
        localName' =
      MachineInterfaceFormalizationTargetUp.mk targetName namespaceRow registry skeleton
        dependencies expectedStatus auditGate notClaimed transport route provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTargetName
  cases hNamespace
  cases hRegistry
  cases hSkeleton
  cases hDependencies
  cases hExpectedStatus
  cases hAuditGate
  cases hNotClaimed
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hLocalName
  rfl

def machineInterfaceFormalizationTargetFields :
    MachineInterfaceFormalizationTargetUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MachineInterfaceFormalizationTargetUp.mk targetName namespaceRow registry skeleton dependencies
      expectedStatus auditGate notClaimed transport route provenance localName =>
      [targetName, namespaceRow, registry, skeleton, dependencies, expectedStatus, auditGate,
        notClaimed, transport, route, provenance, localName]

def machineInterfaceFormalizationTargetToEventFlow :
    MachineInterfaceFormalizationTargetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MachineInterfaceFormalizationTargetUp.mk targetName namespaceRow registry skeleton dependencies
      expectedStatus auditGate notClaimed transport route provenance localName =>
      [machineInterfaceFormalizationTargetEncodeBHist targetName,
        machineInterfaceFormalizationTargetEncodeBHist namespaceRow,
        machineInterfaceFormalizationTargetEncodeBHist registry,
        machineInterfaceFormalizationTargetEncodeBHist skeleton,
        machineInterfaceFormalizationTargetEncodeBHist dependencies,
        machineInterfaceFormalizationTargetEncodeBHist expectedStatus,
        machineInterfaceFormalizationTargetEncodeBHist auditGate,
        machineInterfaceFormalizationTargetEncodeBHist notClaimed,
        machineInterfaceFormalizationTargetEncodeBHist transport,
        machineInterfaceFormalizationTargetEncodeBHist route,
        machineInterfaceFormalizationTargetEncodeBHist provenance,
        machineInterfaceFormalizationTargetEncodeBHist localName]

def machineInterfaceFormalizationTargetFromEventFlow :
    EventFlow → Option MachineInterfaceFormalizationTargetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MachineInterfaceFormalizationTargetUp.mk
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 0 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 1 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 2 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 3 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 4 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 5 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 6 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 7 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 8 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 9 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 10 ef))
        (machineInterfaceFormalizationTargetDecodeBHist
          (machineInterfaceFormalizationTargetRawAt 11 ef)))

private theorem machineInterfaceFormalizationTarget_round_trip :
    ∀ x : MachineInterfaceFormalizationTargetUp,
      machineInterfaceFormalizationTargetFromEventFlow
        (machineInterfaceFormalizationTargetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk targetName namespaceRow registry skeleton dependencies expectedStatus auditGate notClaimed
      transport route provenance localName =>
      exact
        congrArg some
          (machineInterfaceFormalizationTarget_mk_congr
            (machineInterfaceFormalizationTargetDecode_encode_bhist targetName)
            (machineInterfaceFormalizationTargetDecode_encode_bhist namespaceRow)
            (machineInterfaceFormalizationTargetDecode_encode_bhist registry)
            (machineInterfaceFormalizationTargetDecode_encode_bhist skeleton)
            (machineInterfaceFormalizationTargetDecode_encode_bhist dependencies)
            (machineInterfaceFormalizationTargetDecode_encode_bhist expectedStatus)
            (machineInterfaceFormalizationTargetDecode_encode_bhist auditGate)
            (machineInterfaceFormalizationTargetDecode_encode_bhist notClaimed)
            (machineInterfaceFormalizationTargetDecode_encode_bhist transport)
            (machineInterfaceFormalizationTargetDecode_encode_bhist route)
            (machineInterfaceFormalizationTargetDecode_encode_bhist provenance)
            (machineInterfaceFormalizationTargetDecode_encode_bhist localName))

private theorem machineInterfaceFormalizationTargetToEventFlow_injective
    {x y : MachineInterfaceFormalizationTargetUp} :
    machineInterfaceFormalizationTargetToEventFlow x =
      machineInterfaceFormalizationTargetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          machineInterfaceFormalizationTargetFromEventFlow
            (machineInterfaceFormalizationTargetToEventFlow x) :=
        (machineInterfaceFormalizationTarget_round_trip x).symm
      _ =
          machineInterfaceFormalizationTargetFromEventFlow
            (machineInterfaceFormalizationTargetToEventFlow y) :=
        congrArg machineInterfaceFormalizationTargetFromEventFlow hxy
      _ = some y := machineInterfaceFormalizationTarget_round_trip y
  exact Option.some.inj optionEq

private theorem machineInterfaceFormalizationTarget_field_faithful :
    ∀ x y : MachineInterfaceFormalizationTargetUp,
      machineInterfaceFormalizationTargetFields x =
        machineInterfaceFormalizationTargetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk targetName1 namespaceRow1 registry1 skeleton1 dependencies1 expectedStatus1 auditGate1
      notClaimed1 transport1 route1 provenance1 localName1 =>
      cases y with
      | mk targetName2 namespaceRow2 registry2 skeleton2 dependencies2 expectedStatus2 auditGate2
          notClaimed2 transport2 route2 provenance2 localName2 =>
          injection h with hTargetName t1
          injection t1 with hNamespace t2
          injection t2 with hRegistry t3
          injection t3 with hSkeleton t4
          injection t4 with hDependencies t5
          injection t5 with hExpectedStatus t6
          injection t6 with hAuditGate t7
          injection t7 with hNotClaimed t8
          injection t8 with hTransport t9
          injection t9 with hRoute t10
          injection t10 with hProvenance t11
          injection t11 with hLocalName _
          cases hTargetName
          cases hNamespace
          cases hRegistry
          cases hSkeleton
          cases hDependencies
          cases hExpectedStatus
          cases hAuditGate
          cases hNotClaimed
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hLocalName
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
    change machineInterfaceFormalizationTargetFromEventFlow
      (machineInterfaceFormalizationTargetToEventFlow x) = some x
    exact machineInterfaceFormalizationTarget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineInterfaceFormalizationTargetToEventFlow_injective heq)

instance machineInterfaceFormalizationTargetNontrivial :
    Nontrivial MachineInterfaceFormalizationTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineInterfaceFormalizationTargetUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MachineInterfaceFormalizationTargetUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

instance machineInterfaceFormalizationTargetFieldFaithful :
    FieldFaithful MachineInterfaceFormalizationTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := machineInterfaceFormalizationTargetFields
  field_faithful := machineInterfaceFormalizationTarget_field_faithful

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
            machineInterfaceFormalizationTargetToEventFlow y → x = y) ∧
          machineInterfaceFormalizationTargetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨machineInterfaceFormalizationTargetDecode_encode_bhist,
      machineInterfaceFormalizationTarget_round_trip,
      (fun _ _ heq => machineInterfaceFormalizationTargetToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MachineInterfaceFormalizationTargetUp
