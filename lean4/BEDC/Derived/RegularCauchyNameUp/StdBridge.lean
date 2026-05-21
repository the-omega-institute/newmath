import BEDC.Derived.RegularCauchyNameUp

namespace BEDC.Derived.RegularCauchyNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyNameUp_concrete_to_schema [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint standardRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg →
      Cont endpoint provenance standardRead →
        PkgSig bundle standardRead pkg →
          UnaryHistory schedule ∧ UnaryHistory radius ∧ UnaryHistory sealRow ∧
            UnaryHistory endpoint ∧ UnaryHistory standardRead ∧
              hsame radius (append schedule observation) ∧
                hsame sealRow (append radius ledger) ∧
                  hsame endpoint (append sealRow provenance) ∧
                    hsame standardRead (append endpoint provenance) ∧
                      Cont endpoint provenance standardRead ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle standardRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier standardReadRoute standardReadPkg
  obtain ⟨scheduleUnary, _observationUnary, radiusUnary, _ledgerUnary, sealUnary,
    provenanceUnary, _namecertUnary, scheduleObservationRadius, radiusLedgerSeal,
    sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceEndpoint
  have standardReadUnary : UnaryHistory standardRead :=
    unary_cont_closed endpointUnary provenanceUnary standardReadRoute
  exact
    ⟨scheduleUnary, radiusUnary, sealUnary, endpointUnary, standardReadUnary,
      scheduleObservationRadius, radiusLedgerSeal, sealProvenanceEndpoint,
      standardReadRoute, standardReadRoute, endpointPkg, standardReadPkg⟩

end BEDC.Derived.RegularCauchyNameUp
