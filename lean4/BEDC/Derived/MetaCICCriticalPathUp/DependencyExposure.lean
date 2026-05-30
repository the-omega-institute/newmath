import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathNormalizationFrontierDependencyExposure
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceLedger frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      hsame sourceLedger handoff ->
        Cont strongNorm normalForm frontierRead ->
          PkgSig bundle frontierRead pkg ->
            UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory handoff ∧
              UnaryHistory sourceLedger ∧ UnaryHistory frontierRead ∧
                Cont strongNorm normalForm route ∧ Cont strongNorm normalForm frontierRead ∧
                  hsame sourceLedger handoff ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle frontierRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory hsame PkgSig
  intro packet sourceLedgerHandoff strongNormNormalFormFrontier frontierReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_transport handoffUnary (hsame_symm sourceLedgerHandoff)
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormFrontier
  exact
    ⟨strongNormUnary, normalFormUnary, handoffUnary, sourceLedgerUnary, frontierReadUnary,
      strongNormNormalFormRoute, strongNormNormalFormFrontier, sourceLedgerHandoff,
      provenancePkg, frontierReadPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
