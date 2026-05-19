import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_host_obligation_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream hostRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports downstream →
          Cont downstream routes hostRead →
            Cont typed fuel terminalRead →
              PkgSig bundle hostRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row normalRead ∨ hsame row downstream ∨ hsame row hostRead)
                    (fun row : BHist =>
                      hsame row hostRead ∧ PkgSig bundle hostRead pkg)
                    hsame ∧
                  UnaryHistory normalRead ∧ UnaryHistory downstream ∧
                    UnaryHistory hostRead ∧ hsame terminalRead terminal ∧
                      Cont terminal normal continuation ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamRoutesHost
    typedFuelTerminalRead hostReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesHost
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normalRead ∨ hsame row downstream ∨ hsame row hostRead)
          (fun row : BHist => hsame row hostRead ∧ PkgSig bundle hostRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro hostRead ⟨hsame_refl hostRead, hostReadUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, hostReadPkg⟩
  }
  exact
    ⟨cert, normalReadUnary, downstreamUnary, hostReadUnary, terminalReadSame,
      terminalNormalContinuation, provenancePkg⟩

end BEDC.Derived.ZnormalUp
