import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapFamilyUp : Type where
  | mk :
      (familyTag inventory obstruction routing frontier transport replay provenance
        localName : BHist) →
      AuditMapFamilyUp
  deriving DecidableEq

def auditMapFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapFamilyEncodeBHist h

def auditMapFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapFamilyDecodeBHist tail)

private theorem auditMapFamilyDecode_encode_bhist :
    ∀ h : BHist, auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditMapFamilyFields : AuditMapFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFamilyUp.mk familyTag inventory obstruction routing frontier transport replay
      provenance localName =>
      [familyTag, inventory, obstruction, routing, frontier, transport, replay, provenance,
        localName]

def auditMapFamilyToEventFlow : AuditMapFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapFamilyUp.mk familyTag inventory obstruction routing frontier transport replay
      provenance localName =>
      [[BMark.b0],
        auditMapFamilyEncodeBHist familyTag,
        [BMark.b1, BMark.b0],
        auditMapFamilyEncodeBHist inventory,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyEncodeBHist routing,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapFamilyEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapFamilyEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapFamilyEncodeBHist localName]

def auditMapFamilyFromEventFlow : EventFlow → Option AuditMapFamilyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | familyTag :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | inventory :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | obstruction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routing :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | frontier :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (AuditMapFamilyUp.mk
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    familyTag)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    inventory)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    obstruction)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    routing)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    frontier)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    transport)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    replay)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    provenance)
                                                                                  (auditMapFamilyDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem auditMapFamily_round_trip :
    ∀ x : AuditMapFamilyUp,
      auditMapFamilyFromEventFlow (auditMapFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk familyTag inventory obstruction routing frontier transport replay provenance
      localName =>
      change
        some
          (AuditMapFamilyUp.mk
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist familyTag))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist inventory))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist obstruction))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist routing))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist frontier))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist transport))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist replay))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist provenance))
            (auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist localName))) =
          some
            (AuditMapFamilyUp.mk familyTag inventory obstruction routing frontier transport
              replay provenance localName)
      rw [auditMapFamilyDecode_encode_bhist familyTag,
        auditMapFamilyDecode_encode_bhist inventory,
        auditMapFamilyDecode_encode_bhist obstruction,
        auditMapFamilyDecode_encode_bhist routing,
        auditMapFamilyDecode_encode_bhist frontier,
        auditMapFamilyDecode_encode_bhist transport,
        auditMapFamilyDecode_encode_bhist replay,
        auditMapFamilyDecode_encode_bhist provenance,
        auditMapFamilyDecode_encode_bhist localName]

private theorem auditMapFamilyToEventFlow_injective {x y : AuditMapFamilyUp} :
    auditMapFamilyToEventFlow x = auditMapFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapFamilyFromEventFlow (auditMapFamilyToEventFlow x) =
        auditMapFamilyFromEventFlow (auditMapFamilyToEventFlow y) :=
    congrArg auditMapFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapFamily_round_trip x).symm
      (Eq.trans hread (auditMapFamily_round_trip y)))

private theorem AuditMapFamilyTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : AuditMapFamilyUp, auditMapFamilyFields x = auditMapFamilyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk familyTag inventory obstruction routing frontier transport replay provenance localName =>
      cases y with
      | mk familyTag' inventory' obstruction' routing' frontier' transport' replay'
          provenance' localName' =>
          injection hfields with hFamilyTag hTail0
          injection hTail0 with hInventory hTail1
          injection hTail1 with hObstruction hTail2
          injection hTail2 with hRouting hTail3
          injection hTail3 with hFrontier hTail4
          injection hTail4 with hTransport hTail5
          injection hTail5 with hReplay hTail6
          injection hTail6 with hProvenance hTail7
          injection hTail7 with hLocalName _hNil
          cases hFamilyTag
          cases hInventory
          cases hObstruction
          cases hRouting
          cases hFrontier
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hLocalName
          rfl

instance auditMapFamilyBHistCarrier : BHistCarrier AuditMapFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapFamilyToEventFlow
  fromEventFlow := auditMapFamilyFromEventFlow

instance auditMapFamilyChapterTasteGate : ChapterTasteGate AuditMapFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapFamilyFromEventFlow (auditMapFamilyToEventFlow x) = some x
    exact auditMapFamily_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapFamilyToEventFlow_injective heq)

instance auditMapFamilyFieldFaithful : FieldFaithful AuditMapFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapFamilyFields
  field_faithful := AuditMapFamilyTasteGate_single_carrier_alignment_field_faithful

def taste_gate : ChapterTasteGate AuditMapFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapFamilyChapterTasteGate

def AuditMapFamilyCarrier [AskSetup] [PackageSetup]
    (familyTag inventory obstruction routing frontier transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory familyTag ∧ UnaryHistory inventory ∧ UnaryHistory obstruction ∧
    UnaryHistory routing ∧ UnaryHistory frontier ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont familyTag inventory transport ∧ Cont obstruction routing replay ∧
          PkgSig bundle provenance pkg

theorem AuditMapFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditMapFamilyDecodeBHist (auditMapFamilyEncodeBHist h) = h) ∧
      (∀ x : AuditMapFamilyUp,
        auditMapFamilyFromEventFlow (auditMapFamilyToEventFlow x) = some x) ∧
        (∀ x y : AuditMapFamilyUp,
          auditMapFamilyToEventFlow x = auditMapFamilyToEventFlow y → x = y) ∧
          auditMapFamilyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapFamilyDecode_encode_bhist
  · constructor
    · exact auditMapFamily_round_trip
    · constructor
      · intro x y heq
        exact auditMapFamilyToEventFlow_injective heq
      · rfl

theorem AuditMapFamily_tastegate_primality_commitment :
    Nonempty (FieldFaithful AuditMapFamilyUp) ∧
      AuditMapFamilyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty ≠
        AuditMapFamilyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨auditMapFamilyFieldFaithful⟩
  · intro h
    cases h

theorem AuditMapFamilyInventoryFactorization [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg →
      Cont replay localName route →
        PkgSig bundle route pkg →
          UnaryHistory familyTag ∧ UnaryHistory inventory ∧ UnaryHistory obstruction ∧
            UnaryHistory routing ∧ UnaryHistory frontier ∧ UnaryHistory route ∧
              Cont familyTag inventory transport ∧ Cont obstruction routing replay ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier replayRoute routePkg
  rcases carrier with
    ⟨familyTagUnary, inventoryUnary, obstructionUnary, routingUnary, frontierUnary,
      _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
      familyInventoryTransport, obstructionRoutingReplay, provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed replayUnary localNameUnary replayRoute
  exact
    ⟨familyTagUnary, inventoryUnary, obstructionUnary, routingUnary, frontierUnary,
      routeUnary, familyInventoryTransport, obstructionRoutingReplay, provenancePkg,
      routePkg⟩

theorem AuditMapFamilyCrossMapNonescape [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      crossRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg →
      Cont routing frontier crossRoute →
        PkgSig bundle crossRoute pkg →
          UnaryHistory familyTag ∧ UnaryHistory inventory ∧ UnaryHistory obstruction ∧
            UnaryHistory routing ∧ UnaryHistory frontier ∧ UnaryHistory crossRoute ∧
              Cont routing frontier crossRoute ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle crossRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routingFrontier crossRoutePkg
  rcases carrier with
    ⟨familyTagUnary, inventoryUnary, obstructionUnary, routingUnary, frontierUnary,
      _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
      _familyInventoryTransport, _obstructionRoutingReplay, provenancePkg⟩
  have crossRouteUnary : UnaryHistory crossRoute :=
    unary_cont_closed routingUnary frontierUnary routingFrontier
  exact
    ⟨familyTagUnary, inventoryUnary, obstructionUnary, routingUnary, frontierUnary,
      crossRouteUnary, routingFrontier, provenancePkg, crossRoutePkg⟩

theorem AuditMapFamilyCarrier_frontier_stability [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      frontier' frontierRead frontierRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg ->
      hsame frontier frontier' ->
        Cont routing frontier frontierRead ->
          Cont routing frontier' frontierRead' ->
            PkgSig bundle frontierRead pkg ->
              PkgSig bundle frontierRead' pkg ->
                UnaryHistory frontier ∧ UnaryHistory frontier' ∧
                  UnaryHistory frontierRead ∧ UnaryHistory frontierRead' ∧
                    hsame frontierRead frontierRead' ∧
                      Cont routing frontier frontierRead ∧
                        Cont routing frontier' frontierRead' ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle frontierRead pkg ∧
                              PkgSig bundle frontierRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier sameFrontier frontierRoute frontierRoute' frontierPkg frontierPkg'
  rcases carrier with
    ⟨_familyTagUnary, _inventoryUnary, _obstructionUnary, routingUnary, frontierUnary,
      _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
      _familyInventoryTransport, _obstructionRoutingReplay, provenancePkg⟩
  have frontierUnary' : UnaryHistory frontier' :=
    unary_transport frontierUnary sameFrontier
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed routingUnary frontierUnary frontierRoute
  have frontierReadUnary' : UnaryHistory frontierRead' :=
    unary_cont_closed routingUnary frontierUnary' frontierRoute'
  have readSame : hsame frontierRead frontierRead' :=
    cont_respects_hsame (hsame_refl routing) sameFrontier frontierRoute frontierRoute'
  exact
    ⟨frontierUnary, frontierUnary', frontierReadUnary, frontierReadUnary', readSame,
      frontierRoute, frontierRoute', provenancePkg, frontierPkg, frontierPkg'⟩

theorem AuditMapFamilyFrontierStability [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      frontierCopy : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg →
      hsame frontier frontierCopy →
        UnaryHistory frontier ∧ UnaryHistory frontierCopy ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame PkgSig
  intro carrier sameFrontier
  rcases carrier with
    ⟨_familyTagUnary, _inventoryUnary, _obstructionUnary, _routingUnary, frontierUnary,
      _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
      _familyInventoryTransport, _obstructionRoutingReplay, provenancePkg⟩
  have frontierCopyUnary : UnaryHistory frontierCopy :=
    unary_transport frontierUnary sameFrontier
  exact ⟨frontierUnary, frontierCopyUnary, provenancePkg⟩

theorem AuditMapFamilyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg →
      Cont replay localName route →
        PkgSig bundle route pkg →
          UnaryHistory familyTag ∧ UnaryHistory inventory ∧ UnaryHistory obstruction ∧
            UnaryHistory routing ∧ UnaryHistory frontier ∧ UnaryHistory transport ∧
              UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
                Cont familyTag inventory transport ∧ Cont obstruction routing replay ∧
                  Cont replay localName route ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier replayRoute routePkg
  rcases carrier with
    ⟨familyTagUnary, inventoryUnary, obstructionUnary, routingUnary, frontierUnary,
      transportUnary, replayUnary, provenanceUnary, localNameUnary,
      familyInventoryTransport, obstructionRoutingReplay, provenancePkg⟩
  exact
    ⟨familyTagUnary, inventoryUnary, obstructionUnary, routingUnary, frontierUnary,
      transportUnary, replayUnary, provenanceUnary, localNameUnary, familyInventoryTransport,
      obstructionRoutingReplay, replayRoute, provenancePkg, routePkg⟩

theorem AuditMapFamilyCarrier_routing_row_exhaustion [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      routingRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg ->
      Cont routing frontier routingRead ->
        Cont replay localName terminalRead ->
          PkgSig bundle routingRead pkg ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory inventory ∧ UnaryHistory routing ∧ UnaryHistory frontier ∧
                UnaryHistory routingRead ∧ UnaryHistory terminalRead ∧
                  Cont routing frontier routingRead ∧ Cont replay localName terminalRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle routingRead pkg ∧
                      PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routingFrontier replayLocal routingPkg terminalPkg
  rcases carrier with
    ⟨_familyTagUnary, inventoryUnary, _obstructionUnary, routingUnary, frontierUnary,
      _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
      _familyInventoryTransport, _obstructionRoutingReplay, provenancePkg⟩
  have routingReadUnary : UnaryHistory routingRead :=
    unary_cont_closed routingUnary frontierUnary routingFrontier
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed replayUnary localNameUnary replayLocal
  exact
    ⟨inventoryUnary, routingUnary, frontierUnary, routingReadUnary, terminalReadUnary,
      routingFrontier, replayLocal, provenancePkg, routingPkg, terminalPkg⟩

theorem AuditMapFamilyCarrier_obstruction_row_exactness [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      obstructionRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg ->
      Cont obstruction routing obstructionRead ->
        Cont replay localName terminalRead ->
          PkgSig bundle obstructionRead pkg ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory obstruction ∧ UnaryHistory routing ∧ UnaryHistory obstructionRead ∧
                UnaryHistory terminalRead ∧ Cont obstruction routing obstructionRead ∧
                  Cont replay localName terminalRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle obstructionRead pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier obstructionRoute terminalRoute obstructionPkg terminalPkg
  rcases carrier with
    ⟨_familyTagUnary, _inventoryUnary, obstructionUnary, routingUnary, _frontierUnary,
      _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
      _familyInventoryTransport, _obstructionRoutingReplay, provenancePkg⟩
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary routingUnary obstructionRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed replayUnary localNameUnary terminalRoute
  exact
    ⟨obstructionUnary, routingUnary, obstructionReadUnary, terminalReadUnary,
      obstructionRoute, terminalRoute, provenancePkg, obstructionPkg, terminalPkg⟩

theorem AuditMapFamilyCarrier_frontier_nonescape [AskSetup] [PackageSetup]
    {familyTag inventory obstruction routing frontier transport replay provenance localName
      frontierRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier familyTag inventory obstruction routing frontier transport replay
        provenance localName bundle pkg ->
      Cont routing frontier frontierRead ->
        Cont replay localName terminalRead ->
          PkgSig bundle frontierRead pkg ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory frontier ∧ UnaryHistory frontierRead ∧
                UnaryHistory terminalRead ∧ Cont routing frontier frontierRead ∧
                  Cont replay localName terminalRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle frontierRead pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier frontierRoute terminalRoute frontierPkg terminalPkg
  rcases carrier with
    ⟨_familyTagUnary, _inventoryUnary, _obstructionUnary, routingUnary, frontierUnary,
      _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
      _familyInventoryTransport, _obstructionRoutingReplay, provenancePkg⟩
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed routingUnary frontierUnary frontierRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed replayUnary localNameUnary terminalRoute
  exact
    ⟨frontierUnary, frontierReadUnary, terminalReadUnary, frontierRoute, terminalRoute,
      provenancePkg, frontierPkg, terminalPkg⟩

theorem AuditMapFamilyObligationUnblockPackage [AskSetup] [PackageSetup]
    {family inventory obstruction route frontier transport continuation provenance localName
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier family inventory obstruction route frontier transport continuation
        provenance localName bundle pkg →
      Cont route continuation auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row localName ∧
                  AuditMapFamilyCarrier family inventory obstruction route frontier transport
                    continuation provenance localName bundle pkg)
              (fun row : BHist => hsame row localName ∧ Cont route continuation auditRead)
              (fun row : BHist => hsame row localName ∧ PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory family ∧ UnaryHistory inventory ∧ UnaryHistory obstruction ∧
              UnaryHistory route ∧ UnaryHistory frontier ∧ UnaryHistory transport ∧
                UnaryHistory continuation ∧ UnaryHistory provenance ∧
                  UnaryHistory localName ∧ UnaryHistory auditRead ∧
                    Cont route continuation auditRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeContinuation auditPkg
  have carrierWitness := carrier
  obtain ⟨familyUnary, inventoryUnary, obstructionUnary, routeUnary, frontierUnary,
    transportUnary, continuationUnary, provenanceUnary, localNameUnary,
    _familyInventoryTransport, _obstructionRouteContinuation, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary continuationUnary routeContinuation
  have sourceAtName :
      hsame localName localName ∧
        AuditMapFamilyCarrier family inventory obstruction route frontier transport
          continuation provenance localName bundle pkg :=
    And.intro (hsame_refl localName) carrierWitness
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              AuditMapFamilyCarrier family inventory obstruction route frontier transport
                continuation provenance localName bundle pkg)
          (fun row : BHist => hsame row localName ∧ Cont route continuation auditRead)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceAtName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left routeContinuation
    ledger_sound := by
      intro _row source
      exact And.intro source.left auditPkg
  }
  exact
    ⟨cert, familyUnary, inventoryUnary, obstructionUnary, routeUnary, frontierUnary,
      transportUnary, continuationUnary, provenanceUnary, localNameUnary, auditUnary,
      routeContinuation, provenancePkg, auditPkg⟩

end BEDC.Derived.AuditMapFamilyUp
