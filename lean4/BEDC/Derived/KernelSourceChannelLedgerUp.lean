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

end BEDC.Derived.KernelSourceChannelLedgerUp
