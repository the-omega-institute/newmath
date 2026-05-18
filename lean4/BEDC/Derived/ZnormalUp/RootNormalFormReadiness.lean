import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootNormalFormReadiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead sourceRead sourceExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont normal continuation normalRead →
          Cont typed fuel sourceRead →
            Cont sourceRead name sourceExport →
              PkgSig bundle sourceExport pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sourceExport ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
                        hsame row sourceExport)
                    (fun row : BHist =>
                      hsame row sourceExport ∧ PkgSig bundle sourceExport pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                    UnaryHistory normalRead ∧ UnaryHistory sourceRead ∧
                      UnaryHistory sourceExport ∧ Cont terminal normal continuation ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle sourceExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead normalContinuationRead typedFuelSourceRead
    sourceReadNameSourceExport sourceExportPkg
  have packetWitness := packet
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  obtain ⟨terminalReadSame, terminalReadUnary, terminalNormalContinuation,
    provenancePkg⟩ :=
    ZnormalPacket_root_terminal_normality_determinacy packetWitness typedFuelTerminalRead
  obtain ⟨sourceCert, sourceReadUnary, sourceExportUnary⟩ :=
    ZnormalPacket_root_total_host_source_coverage packetWitness typedFuelSourceRead
      sourceReadNameSourceExport sourceExportPkg
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  exact
    ⟨sourceCert, terminalReadSame, terminalReadUnary, normalReadUnary, sourceReadUnary,
      sourceExportUnary, terminalNormalContinuation, provenancePkg, sourceExportPkg⟩

end BEDC.Derived.ZnormalUp
