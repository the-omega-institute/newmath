import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HostDelegationSocketUp

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

inductive HostDelegationSocketUp : Type where
  | mk :
      (marker audit kernel target transport continuation provenance ledger name : BHist) →
      HostDelegationSocketUp
  deriving DecidableEq

def hostDelegationSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hostDelegationSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hostDelegationSocketEncodeBHist h

def hostDelegationSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hostDelegationSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hostDelegationSocketDecodeBHist tail)

private theorem hostDelegationSocket_decode_encode_bhist :
    ∀ h : BHist, hostDelegationSocketDecodeBHist (hostDelegationSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem hostDelegationSocket_mk_congr
    {marker marker' audit audit' kernel kernel' target target'
      transport transport' continuation continuation' provenance provenance'
      ledger ledger' name name' : BHist}
    (hMarker : marker' = marker)
    (hAudit : audit' = audit)
    (hKernel : kernel' = kernel)
    (hTarget : target' = target)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLedger : ledger' = ledger)
    (hName : name' = name) :
    HostDelegationSocketUp.mk marker' audit' kernel' target' transport'
        continuation' provenance' ledger' name' =
      HostDelegationSocketUp.mk marker audit kernel target transport continuation
        provenance ledger name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMarker
  cases hAudit
  cases hKernel
  cases hTarget
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLedger
  cases hName
  rfl

def hostDelegationSocketToEventFlow : HostDelegationSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HostDelegationSocketUp.mk marker audit kernel target transport continuation
      provenance ledger name =>
      [[BMark.b0],
        hostDelegationSocketEncodeBHist marker,
        [BMark.b1, BMark.b0],
        hostDelegationSocketEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b0],
        hostDelegationSocketEncodeBHist kernel,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostDelegationSocketEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostDelegationSocketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostDelegationSocketEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostDelegationSocketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hostDelegationSocketEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hostDelegationSocketEncodeBHist name]

def hostDelegationSocketFromEventFlow : EventFlow → Option HostDelegationSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | marker :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | audit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | kernel :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | target :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | ledger :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (HostDelegationSocketUp.mk
                                                                                  (hostDelegationSocketDecodeBHist marker)
                                                                                  (hostDelegationSocketDecodeBHist audit)
                                                                                  (hostDelegationSocketDecodeBHist kernel)
                                                                                  (hostDelegationSocketDecodeBHist target)
                                                                                  (hostDelegationSocketDecodeBHist transport)
                                                                                  (hostDelegationSocketDecodeBHist continuation)
                                                                                  (hostDelegationSocketDecodeBHist provenance)
                                                                                  (hostDelegationSocketDecodeBHist ledger)
                                                                                  (hostDelegationSocketDecodeBHist name))
                                                                          | _ :: _ => none

private theorem hostDelegationSocket_round_trip :
    ∀ x : HostDelegationSocketUp,
      hostDelegationSocketFromEventFlow (hostDelegationSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk marker audit kernel target transport continuation provenance ledger name =>
      change
        some
          (HostDelegationSocketUp.mk
            (hostDelegationSocketDecodeBHist (hostDelegationSocketEncodeBHist marker))
            (hostDelegationSocketDecodeBHist (hostDelegationSocketEncodeBHist audit))
            (hostDelegationSocketDecodeBHist (hostDelegationSocketEncodeBHist kernel))
            (hostDelegationSocketDecodeBHist (hostDelegationSocketEncodeBHist target))
            (hostDelegationSocketDecodeBHist
              (hostDelegationSocketEncodeBHist transport))
            (hostDelegationSocketDecodeBHist
              (hostDelegationSocketEncodeBHist continuation))
            (hostDelegationSocketDecodeBHist
              (hostDelegationSocketEncodeBHist provenance))
            (hostDelegationSocketDecodeBHist (hostDelegationSocketEncodeBHist ledger))
            (hostDelegationSocketDecodeBHist (hostDelegationSocketEncodeBHist name))) =
          some
            (HostDelegationSocketUp.mk marker audit kernel target transport continuation
              provenance ledger name)
      exact
        congrArg some
          (hostDelegationSocket_mk_congr
            (hostDelegationSocket_decode_encode_bhist marker)
            (hostDelegationSocket_decode_encode_bhist audit)
            (hostDelegationSocket_decode_encode_bhist kernel)
            (hostDelegationSocket_decode_encode_bhist target)
            (hostDelegationSocket_decode_encode_bhist transport)
            (hostDelegationSocket_decode_encode_bhist continuation)
            (hostDelegationSocket_decode_encode_bhist provenance)
            (hostDelegationSocket_decode_encode_bhist ledger)
            (hostDelegationSocket_decode_encode_bhist name))

private theorem hostDelegationSocketToEventFlow_injective {x y : HostDelegationSocketUp} :
    hostDelegationSocketToEventFlow x = hostDelegationSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hostDelegationSocketFromEventFlow (hostDelegationSocketToEventFlow x) =
        hostDelegationSocketFromEventFlow (hostDelegationSocketToEventFlow y) :=
    congrArg hostDelegationSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hostDelegationSocket_round_trip x).symm
      (Eq.trans hread (hostDelegationSocket_round_trip y)))

instance hostDelegationSocketBHistCarrier : BHistCarrier HostDelegationSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hostDelegationSocketToEventFlow
  fromEventFlow := hostDelegationSocketFromEventFlow

instance hostDelegationSocketChapterTasteGate : ChapterTasteGate HostDelegationSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hostDelegationSocketFromEventFlow (hostDelegationSocketToEventFlow x) = some x
    exact hostDelegationSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hostDelegationSocketToEventFlow_injective heq)

theorem HostDelegationSocket_marker_boundary
    {marker audit kernel target transport continuation provenance ledger name marker' audit'
      kernel' target' transport' continuation' provenance' ledger' name' : BHist} :
    hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name) =
      hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name') →
      Cont marker target ledger →
        hsame marker marker' ∧ hsame target target' ∧ hsame kernel kernel' ∧
          hsame ledger ledger' ∧ Cont marker' target' ledger' := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro encodedSame markerTargetLedger
  have carrierSame :
      HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name =
        HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name' :=
    hostDelegationSocketToEventFlow_injective encodedSame
  cases carrierSame
  exact
    ⟨hsame_refl marker, hsame_refl target, hsame_refl kernel, hsame_refl ledger,
      markerTargetLedger⟩

theorem HostDelegationSocketNonEscape [AskSetup] [PackageSetup]
    {marker audit kernel target transport continuation provenance ledger name marker' audit'
      kernel' target' transport' continuation' provenance' ledger' name' consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name) =
      hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name') →
      Cont marker target ledger →
        Cont ledger name consumer →
          PkgSig bundle provenance pkg →
            hsame marker marker' ∧ hsame audit audit' ∧ hsame kernel kernel' ∧
              hsame target target' ∧ hsame transport transport' ∧
                hsame continuation continuation' ∧ hsame provenance provenance' ∧
                  hsame ledger ledger' ∧ hsame name name' ∧
                    Cont marker' target' ledger' ∧ Cont ledger' name' consumer ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame PkgSig ProbeBundle
  intro encodedSame markerTargetLedger ledgerNameConsumer provenancePkg
  have carrierSame :
      HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name =
        HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name' :=
    hostDelegationSocketToEventFlow_injective encodedSame
  cases carrierSame
  exact
    ⟨hsame_refl marker, hsame_refl audit, hsame_refl kernel, hsame_refl target,
      hsame_refl transport, hsame_refl continuation, hsame_refl provenance,
      hsame_refl ledger, hsame_refl name, markerTargetLedger, ledgerNameConsumer,
      provenancePkg⟩

theorem HostDelegationSocket_audit_face_separation [AskSetup] [PackageSetup]
    {marker audit kernel target transport continuation provenance ledger name marker' audit'
      kernel' target' transport' continuation' provenance' ledger' name' auditEvidence
      kernelEvidence : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name) =
      hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name') →
      Cont audit transport auditEvidence →
        Cont kernel target kernelEvidence →
          PkgSig bundle provenance pkg →
            hsame audit audit' ∧ hsame kernel kernel' ∧
              Cont audit' transport' auditEvidence ∧
                Cont kernel' target' kernelEvidence ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame ProbeBundle Pkg PkgSig
  intro encodedSame auditRoute kernelRoute provenancePkg
  have carrierSame :
      HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name =
        HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name' :=
    hostDelegationSocketToEventFlow_injective encodedSame
  cases carrierSame
  exact
    ⟨hsame_refl audit, hsame_refl kernel, auditRoute, kernelRoute, provenancePkg⟩

theorem HostDelegationSocketPrimitiveScopeBinding [AskSetup] [PackageSetup]
    {marker audit kernel target transport continuation provenance ledger name marker' audit'
      kernel' target' transport' continuation' provenance' ledger' name' markerRead auditRead
      kernelRead targetRead provenanceRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name) =
      hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name') →
      Cont marker target markerRead →
        Cont audit transport auditRead →
          Cont kernel target kernelRead →
            Cont target continuation targetRead →
              Cont provenance name provenanceRead →
                Cont ledger name ledgerRead →
                  PkgSig bundle provenance pkg →
                    hsame marker marker' ∧ hsame audit audit' ∧ hsame kernel kernel' ∧
                      hsame target target' ∧ hsame provenance provenance' ∧
                        hsame ledger ledger' ∧ Cont marker' target' markerRead ∧
                          Cont audit' transport' auditRead ∧
                            Cont kernel' target' kernelRead ∧
                              Cont target' continuation' targetRead ∧
                                Cont provenance' name' provenanceRead ∧
                                  Cont ledger' name' ledgerRead ∧
                                    PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame ProbeBundle Pkg PkgSig
  intro encodedSame markerRoute auditRoute kernelRoute targetRoute provenanceRoute ledgerRoute
    provenancePkg
  have carrierSame :
      HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name =
        HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name' :=
    hostDelegationSocketToEventFlow_injective encodedSame
  cases carrierSame
  exact
    ⟨hsame_refl marker, hsame_refl audit, hsame_refl kernel, hsame_refl target,
      hsame_refl provenance, hsame_refl ledger, markerRoute, auditRoute, kernelRoute,
      targetRoute, provenanceRoute, ledgerRoute, provenancePkg⟩

theorem HostDelegationSocket_marker_audit_consumer [AskSetup] [PackageSetup]
    {marker audit kernel target transport continuation provenance ledger name marker' audit'
      kernel' target' transport' continuation' provenance' ledger' name' auditRead kernelRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name) =
      hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name') →
      Cont marker target ledger →
        Cont audit transport auditRead →
          Cont kernel target kernelRead →
            PkgSig bundle provenance pkg →
              hsame marker marker' ∧ hsame target target' ∧ hsame kernel kernel' ∧
                hsame ledger ledger' ∧ Cont marker' target' ledger' ∧
                  Cont audit' transport' auditRead ∧ Cont kernel' target' kernelRead ∧
                    PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: HostDelegationSocket_marker_boundary BHist Cont hsame PkgSig
  intro encodedSame markerRoute auditRoute kernelRoute provenancePkg
  have markerBoundary :=
    HostDelegationSocket_marker_boundary
      (marker := marker) (audit := audit) (kernel := kernel) (target := target)
      (transport := transport) (continuation := continuation) (provenance := provenance)
      (ledger := ledger) (name := name) (marker' := marker') (audit' := audit')
      (kernel' := kernel') (target' := target') (transport' := transport')
      (continuation' := continuation') (provenance' := provenance') (ledger' := ledger')
      (name' := name') encodedSame markerRoute
  have auditKernel :=
    HostDelegationSocket_audit_face_separation
      (marker := marker) (audit := audit) (kernel := kernel) (target := target)
      (transport := transport) (continuation := continuation) (provenance := provenance)
      (ledger := ledger) (name := name) (marker' := marker') (audit' := audit')
      (kernel' := kernel') (target' := target') (transport' := transport')
      (continuation' := continuation') (provenance' := provenance') (ledger' := ledger')
      (name' := name') (auditEvidence := auditRead) (kernelEvidence := kernelRead)
      encodedSame auditRoute kernelRoute provenancePkg
  exact
    ⟨markerBoundary.left, markerBoundary.right.left, markerBoundary.right.right.left,
      markerBoundary.right.right.right.left, markerBoundary.right.right.right.right,
      auditKernel.right.right.left, auditKernel.right.right.right.left,
      auditKernel.right.right.right.right⟩

def HostDelegationSocketCarrier [AskSetup] [PackageSetup]
    (marker audit kernel target transport continuation provenance ledger name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory marker ∧ UnaryHistory audit ∧ UnaryHistory kernel ∧ UnaryHistory target ∧
    UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
      UnaryHistory ledger ∧ UnaryHistory name ∧ Cont marker target ledger ∧
        Cont ledger name continuation ∧ PkgSig bundle name pkg

theorem HostDelegationSocketCarrier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {marker audit kernel target transport continuation provenance ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HostDelegationSocketCarrier marker audit kernel target transport continuation provenance ledger
        name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          HostDelegationSocketCarrier marker audit kernel target transport continuation provenance
            ledger name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          Cont marker target ledger ∧ Cont ledger name continuation ∧ hsame row name)
        (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_markerUnary, _auditUnary, _kernelUnary, _targetUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _ledgerUnary, _nameUnary, markerTargetLedger,
    ledgerNameContinuation, namePkg⟩ := carrier
  have core :
      NameCert
        (fun row : BHist =>
          HostDelegationSocketCarrier marker audit kernel target transport continuation provenance
            ledger name bundle pkg ∧ hsame row name)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro name
        (And.intro carrierWitness (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  exact {
    core := core
    pattern_sound := by
      intro _row sourceRow
      exact ⟨markerTargetLedger, ledgerNameContinuation, sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨namePkg, sourceRow.right⟩
  }

theorem HostDelegationSocket_public_interface [AskSetup] [PackageSetup]
    {marker audit kernel target transport continuation provenance ledger name marker' audit'
      kernel' target' transport' continuation' provenance' ledger' name' markerRead auditRead
      kernelRead targetRead provenanceRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name) =
      hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name') →
      Cont marker target markerRead →
        Cont audit transport auditRead →
          Cont kernel target kernelRead →
            Cont target continuation targetRead →
              Cont provenance name provenanceRead →
                Cont ledger name ledgerRead →
                  PkgSig bundle provenance pkg →
                    hsame marker marker' ∧ hsame audit audit' ∧ hsame kernel kernel' ∧
                      hsame target target' ∧ hsame transport transport' ∧
                        hsame continuation continuation' ∧ hsame provenance provenance' ∧
                          hsame ledger ledger' ∧ hsame name name' ∧
                            Cont marker' target' markerRead ∧
                              Cont audit' transport' auditRead ∧
                                Cont kernel' target' kernelRead ∧
                                  Cont target' continuation' targetRead ∧
                                    Cont provenance' name' provenanceRead ∧
                                      Cont ledger' name' ledgerRead ∧
                                        PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame ProbeBundle Pkg PkgSig
  intro encodedSame markerRoute auditRoute kernelRoute targetRoute provenanceRoute ledgerRoute
    provenancePkg
  have carrierSame :
      HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name =
        HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name' :=
    hostDelegationSocketToEventFlow_injective encodedSame
  cases carrierSame
  exact
    ⟨hsame_refl marker, hsame_refl audit, hsame_refl kernel, hsame_refl target,
      hsame_refl transport, hsame_refl continuation, hsame_refl provenance,
      hsame_refl ledger, hsame_refl name, markerRoute, auditRoute, kernelRoute,
      targetRoute, provenanceRoute, ledgerRoute, provenancePkg⟩

theorem HostDelegationSocket_bridge_interface [AskSetup] [PackageSetup]
    {marker audit kernel target transport continuation provenance ledger name marker' audit'
      kernel' target' transport' continuation' provenance' ledger' name' markerRead auditRead
      kernelRead targetRead ledgerRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name) =
      hostDelegationSocketToEventFlow
        (HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name') →
      Cont marker target markerRead →
        Cont audit transport auditRead →
          Cont kernel target kernelRead →
            Cont target continuation targetRead →
              Cont ledger name ledgerRead →
                Cont ledgerRead name localRead →
                  PkgSig bundle provenance pkg →
                    hsame marker marker' ∧ hsame audit audit' ∧ hsame kernel kernel' ∧
                      hsame target target' ∧ hsame ledger ledger' ∧ hsame name name' ∧
                        Cont marker' target' markerRead ∧
                          Cont audit' transport' auditRead ∧
                            Cont kernel' target' kernelRead ∧
                              Cont target' continuation' targetRead ∧
                                Cont ledger' name' ledgerRead ∧
                                  Cont ledgerRead name' localRead ∧
                                    PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame ProbeBundle Pkg PkgSig
  intro encodedSame markerRoute auditRoute kernelRoute targetRoute ledgerRoute localRoute
    provenancePkg
  have carrierSame :
      HostDelegationSocketUp.mk marker audit kernel target transport continuation provenance
          ledger name =
        HostDelegationSocketUp.mk marker' audit' kernel' target' transport' continuation'
          provenance' ledger' name' :=
    hostDelegationSocketToEventFlow_injective encodedSame
  cases carrierSame
  exact
    ⟨hsame_refl marker, hsame_refl audit, hsame_refl kernel, hsame_refl target,
      hsame_refl ledger, hsame_refl name, markerRoute, auditRoute, kernelRoute,
      targetRoute, ledgerRoute, localRoute, provenancePkg⟩

end BEDC.Derived.HostDelegationSocketUp
