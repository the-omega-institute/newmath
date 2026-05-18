import BEDC.Derived.ZnormalUp.RootContReplayClosure

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootDisplayPacketBridgeReadbackExactness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name replayRead
      replayExport downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont continuation transports replayRead →
        Cont replayRead name replayExport →
          Cont replayExport routes downstream →
            PkgSig bundle replayExport pkg →
              PkgSig bundle downstream pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row replayExport ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row continuation ∨ hsame row transports ∨
                        hsame row replayRead ∨ hsame row replayExport)
                    (fun row : BHist =>
                      PkgSig bundle replayExport pkg ∧ hsame row replayExport)
                    hsame ∧
                  UnaryHistory replayRead ∧ UnaryHistory replayExport ∧
                    UnaryHistory downstream ∧ Cont replayExport routes downstream ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet continuationTransportsReplay replayNameExport replayRoutesDownstream
    replayExportPkg downstreamPkg
  have packetWitness := packet
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  obtain ⟨replayCert, replayReadUnary, replayExportUnary⟩ :=
    ZnormalRootContReplayClosure packetWitness continuationTransportsReplay replayNameExport
      replayExportPkg
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed replayExportUnary routesUnary replayRoutesDownstream
  exact
    ⟨replayCert, replayReadUnary, replayExportUnary, downstreamUnary,
      replayRoutesDownstream, provenancePkg, downstreamPkg⟩

end BEDC.Derived.ZnormalUp
