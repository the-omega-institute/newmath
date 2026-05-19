import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_consumer_factorization [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead downstream consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal normalRead →
          Cont normalRead transports downstream →
            Cont downstream routes consumer →
              PkgSig bundle consumer pkg →
                hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                  UnaryHistory normalRead ∧ UnaryHistory downstream ∧
                    UnaryHistory consumer ∧ Cont typed fuel terminal ∧
                      Cont terminalRead normal normalRead ∧
                        Cont normalRead transports downstream ∧
                          Cont downstream routes consumer ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadTransportsDownstream
    downstreamRoutesConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesConsumer
  exact
    ⟨terminalReadSame, terminalReadUnary, normalReadUnary, downstreamUnary,
      consumerUnary, typedFuelTerminal, terminalReadNormalRead, normalReadTransportsDownstream,
      downstreamRoutesConsumer, provenancePkg, consumerPkg⟩

theorem ZnormalPacket_downstream_normal_route_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead downstream consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal normalRead →
          Cont normalRead transports downstream →
            Cont downstream routes consumer →
              PkgSig bundle consumer pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalRead ∨ hsame row normalRead ∨
                        hsame row downstream ∨ hsame row consumer)
                    (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadTransportsDownstream
    downstreamRoutesConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row terminalRead ∨ hsame row normalRead ∨ hsame row downstream ∨
            hsame row consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact ⟨cert, terminalReadSame, consumerUnary⟩

end BEDC.Derived.ZnormalUp
