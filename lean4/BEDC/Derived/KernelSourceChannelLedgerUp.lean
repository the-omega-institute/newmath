import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KernelSourceChannelLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KernelSourceChannelLedgerPacket [AskSetup] [PackageSetup]
    (generated stamp accepted ancestry query refusal trace route separation transport replay
      provenance name : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory generated ∧ UnaryHistory stamp ∧ UnaryHistory accepted ∧
    UnaryHistory ancestry ∧ UnaryHistory query ∧ UnaryHistory refusal ∧
      UnaryHistory trace ∧ UnaryHistory route ∧ UnaryHistory separation ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory name ∧ Cont generated stamp accepted ∧
            Cont query refusal separation ∧ Cont trace route transport ∧
              Cont transport replay provenance ∧ PkgSig bundle name pkg

theorem KernelSourceChannelLedgerPacket_namecert_obligations [AskSetup] [PackageSetup]
    {generated stamp accepted ancestry query refusal trace route separation transport replay
      provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelSourceChannelLedgerPacket generated stamp accepted ancestry query refusal trace route
        separation transport replay provenance name bundle pkg ->
      UnaryHistory generated ∧ UnaryHistory stamp ∧ UnaryHistory accepted ∧
        UnaryHistory ancestry ∧ UnaryHistory query ∧ UnaryHistory refusal ∧
          Cont generated stamp accepted ∧ Cont query refusal separation ∧
            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨generatedUnary, stampUnary, acceptedUnary, ancestryUnary, queryUnary, refusalUnary,
    _traceUnary, _routeUnary, _separationUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, generatedStampAccepted, queryRefusalSeparation, _traceRouteTransport,
    _transportReplayProvenance, namePkg⟩ := packet
  exact
    ⟨generatedUnary, stampUnary, acceptedUnary, ancestryUnary, queryUnary, refusalUnary,
      generatedStampAccepted, queryRefusalSeparation, namePkg⟩

theorem KernelSourceChannelLedgerPacket_trace_projection [AskSetup] [PackageSetup]
    {generated stamp accepted ancestry query refusal trace route separation transport replay
      provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelSourceChannelLedgerPacket generated stamp accepted ancestry query refusal trace route
        separation transport replay provenance name bundle pkg ->
      UnaryHistory trace ∧ UnaryHistory route ∧ UnaryHistory separation ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory name ∧ Cont trace route transport ∧ Cont transport replay provenance ∧
            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨_generatedUnary, _stampUnary, _acceptedUnary, _ancestryUnary, _queryUnary,
    _refusalUnary, traceUnary, routeUnary, separationUnary, transportUnary, replayUnary,
    provenanceUnary, nameUnary, _generatedStampAccepted, _queryRefusalSeparation,
    traceRouteTransport, transportReplayProvenance, namePkg⟩ := packet
  exact
    ⟨traceUnary, routeUnary, separationUnary, transportUnary, replayUnary, provenanceUnary,
      nameUnary, traceRouteTransport, transportReplayProvenance, namePkg⟩

theorem KernelSourceChannelLedgerPacket_audit_boundary [AskSetup] [PackageSetup]
    {generated stamp accepted ancestry query refusal trace route separation transport replay
      provenance name auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelSourceChannelLedgerPacket generated stamp accepted ancestry query refusal trace route
        separation transport replay provenance name bundle pkg ->
      Cont accepted query auditRead ->
        PkgSig bundle auditRead pkg ->
          UnaryHistory generated ∧ UnaryHistory stamp ∧ UnaryHistory accepted ∧
            UnaryHistory query ∧ UnaryHistory refusal ∧ UnaryHistory auditRead ∧
              Cont generated stamp accepted ∧ Cont query refusal separation ∧
                Cont accepted query auditRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet acceptedQueryAudit auditPkg
  obtain ⟨generatedUnary, stampUnary, acceptedUnary, _ancestryUnary, queryUnary, refusalUnary,
    _traceUnary, _routeUnary, _separationUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, generatedStampAccepted, queryRefusalSeparation, _traceRouteTransport,
    _transportReplayProvenance, namePkg⟩ := packet
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed acceptedUnary queryUnary acceptedQueryAudit
  exact
    ⟨generatedUnary, stampUnary, acceptedUnary, queryUnary, refusalUnary, auditUnary,
      generatedStampAccepted, queryRefusalSeparation, acceptedQueryAudit, namePkg, auditPkg⟩

theorem KernelSourceChannelLedgerPacket_query_refusal_stability [AskSetup] [PackageSetup]
    {generated stamp accepted ancestry query refusal trace route separation transport replay
      provenance name query' refusal' separation' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelSourceChannelLedgerPacket generated stamp accepted ancestry query refusal trace route
        separation transport replay provenance name bundle pkg ->
      hsame query query' ->
        hsame refusal refusal' ->
          Cont query' refusal' separation' ->
            UnaryHistory query' ∧ UnaryHistory refusal' ∧ UnaryHistory separation' ∧
              Cont query' refusal' separation' ∧ Cont generated stamp accepted ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig
  intro packet sameQuery sameRefusal queryRefusalSeparation'
  obtain ⟨_generatedUnary, _stampUnary, _acceptedUnary, _ancestryUnary, queryUnary,
    refusalUnary, _traceUnary, _routeUnary, _separationUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, generatedStampAccepted, _queryRefusalSeparation,
    _traceRouteTransport, _transportReplayProvenance, namePkg⟩ := packet
  have queryUnary' : UnaryHistory query' :=
    unary_transport queryUnary sameQuery
  have refusalUnary' : UnaryHistory refusal' :=
    unary_transport refusalUnary sameRefusal
  have separationUnary' : UnaryHistory separation' :=
    unary_cont_closed queryUnary' refusalUnary' queryRefusalSeparation'
  exact
    ⟨queryUnary', refusalUnary', separationUnary', queryRefusalSeparation',
      generatedStampAccepted, namePkg⟩

end BEDC.Derived.KernelSourceChannelLedgerUp
