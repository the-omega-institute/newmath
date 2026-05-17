import BEDC.Derived.DyadicApproximationUp.FiniteMeshEnclosure

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_dyadicratcore_dependency_route [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg →
      hsame precision terminalPrecision →
        hsame endpoint terminalEndpoint →
          hsame ledger terminalLedger →
            hsame provenance terminalProvenance →
              Cont terminalPrecision terminalEndpoint terminalWindow →
                Cont terminalWindow terminalLedger terminalProvenance →
                  Cont terminalWindow terminalProvenance meshCell →
                    Cont meshCell terminalProvenance enclosure →
                      Cont enclosure terminalProvenance validatedRead →
                        Cont terminalLedger terminalProvenance sealRow →
                          Cont validatedRead sealRow terminalRead →
                            PkgSig bundle meshCell pkg →
                              PkgSig bundle enclosure pkg →
                                PkgSig bundle validatedRead pkg →
                                  PkgSig bundle sealRow pkg →
                                    PkgSig bundle terminalRead pkg →
                                      DyadicApproximationCarrier terminalPrecision
                                          terminalEndpoint terminalWindow terminalLedger
                                          terminalProvenance bundle pkg ∧
                                        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧
                                          UnaryHistory validatedRead ∧ UnaryHistory sealRow ∧
                                            UnaryHistory terminalRead ∧
                                              hsame window terminalWindow ∧
                                                PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal validatedSealTerminal
  intro meshPkg enclosurePkg validatedPkg sealPkg terminalPkg
  have exactness :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory validatedRead ∧
          UnaryHistory sealRow ∧ hsame window terminalWindow ∧
            PkgSig bundle validatedRead pkg :=
    DyadicApproximationCarrier_finite_mesh_enclosure_exactness carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      enclosureProvenanceValidated terminalLedgerProvenanceSeal meshPkg enclosurePkg
      validatedPkg sealPkg
  rcases exactness with
    ⟨terminalCarrier, meshUnary, enclosureUnary, validatedUnary, sealUnary, sameWindow,
      _validatedPkg⟩
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed validatedUnary sealUnary validatedSealTerminal
  exact
    ⟨terminalCarrier, meshUnary, enclosureUnary, validatedUnary, sealUnary, terminalUnary,
      sameWindow, terminalPkg⟩

end BEDC.Derived.DyadicApproximationUp
