import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_readiness_export_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead downstream consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name bundle
        pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal normalRead ->
          Cont normalRead transports downstream ->
            Cont downstream routes consumer ->
              PkgSig bundle consumer pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                        hsame row normalRead ∨ hsame row downstream ∨ hsame row consumer)
                    (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                    UnaryHistory normalRead ∧ UnaryHistory downstream ∧
                      UnaryHistory consumer ∧ Cont typed fuel terminalRead ∧
                        Cont terminalRead normal normalRead ∧
                          Cont normalRead transports downstream ∧
                            Cont downstream routes consumer ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadDownstream
    downstreamRoutesConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadTerminal : hsame terminalRead terminal :=
    hsame_symm (cont_deterministic typedFuelTerminal typedFuelTerminalRead)
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_transport terminalUnary (hsame_symm terminalReadTerminal)
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadDownstream
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
            hsame row normalRead ∨ hsame row downstream ∨ hsame row consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumer (And.intro (hsame_refl consumer) consumerUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro row source
      exact And.intro source.left consumerPkg
  }
  exact
    ⟨cert, terminalReadTerminal, terminalReadUnary, normalReadUnary, downstreamUnary,
      consumerUnary, typedFuelTerminalRead, terminalReadNormalRead, normalReadDownstream,
      downstreamRoutesConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.ZnormalUp
