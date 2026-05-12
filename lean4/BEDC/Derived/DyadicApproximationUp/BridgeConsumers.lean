import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_rational_interval_window_handoff [AskSetup]
    [PackageSetup]
    {precision endpoint window ledger provenance interval containment sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      UnaryHistory interval ->
        Cont endpoint interval containment ->
          Cont ledger provenance sealRead ->
            PkgSig bundle containment pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
                  UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory interval ∧
                    UnaryHistory containment ∧ UnaryHistory sealRead ∧
                      Cont precision endpoint window ∧ Cont window ledger provenance ∧
                        Cont endpoint interval containment ∧
                          Cont ledger provenance sealRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle containment pkg ∧ PkgSig bundle sealRead pkg := by
  intro carrier intervalUnary endpointIntervalContainment ledgerProvenanceSealRead
    containmentPkg sealReadPkg
  obtain ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
    precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩ := carrier
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed endpointUnary intervalUnary endpointIntervalContainment
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceSealRead
  exact
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      intervalUnary, containmentUnary, sealReadUnary, precisionEndpointWindow,
      windowLedgerProvenance, endpointIntervalContainment, ledgerProvenanceSealRead,
      provenancePkg, containmentPkg, sealReadPkg⟩

end BEDC.Derived.DyadicApproximationUp
