import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootReadinessTerminalRefusalClosure [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute siblingRead downstream finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal terminalRoute →
          Cont normal continuation siblingRead →
            Cont siblingRead transports downstream →
              Cont downstream provenance finalRead →
                PkgSig bundle finalRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row typed ∨ hsame row terminalRoute ∨
                          hsame row siblingRead ∨ hsame row finalRead)
                      (fun row : BHist =>
                        hsame row finalRead ∧ PkgSig bundle finalRead pkg)
                      hsame ∧
                    UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalTerminalRoute
    normalContinuationSiblingRead siblingReadTransportsDownstream downstreamProvenanceFinalRead
    finalReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have _terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTerminalRoute
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSiblingRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed siblingReadUnary transportsUnary siblingReadTransportsDownstream
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed downstreamUnary provenanceUnary downstreamProvenanceFinalRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row terminalRoute ∨
              hsame row siblingRead ∨ hsame row finalRead)
          (fun row : BHist =>
            hsame row finalRead ∧ PkgSig bundle finalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finalRead ⟨hsame_refl finalRead, finalReadUnary⟩
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
      exact ⟨source.left, finalReadPkg⟩
  }
  exact ⟨cert, finalReadUnary⟩

end BEDC.Derived.ZnormalUp
