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

theorem RegularCauchyNameUp_StdBridge [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window readback
      sealedRead standardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg →
      Cont schedule observation window →
        Cont window radius readback →
          Cont readback sealRow sealedRead →
            Cont sealedRead provenance standardRead →
              PkgSig bundle standardRead pkg →
                UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory sealedRead ∧
                  UnaryHistory standardRead ∧ hsame window (append schedule observation) ∧
                    hsame readback (append window radius) ∧
                      hsame sealedRead (append readback sealRow) ∧
                        hsame standardRead (append sealedRead provenance) ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle standardRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier scheduleObservationWindow windowRadiusReadback readbackSealSealed
    sealedProvenanceStandard standardPkg
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, sealUnary,
    provenanceUnary, _namecertUnary, _scheduleObservationRadius, _radiusLedgerSeal,
    _sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealSealed
  have standardReadUnary : UnaryHistory standardRead :=
    unary_cont_closed sealedReadUnary provenanceUnary sealedProvenanceStandard
  exact
    ⟨windowUnary, readbackUnary, sealedReadUnary, standardReadUnary,
      scheduleObservationWindow, windowRadiusReadback, readbackSealSealed,
      sealedProvenanceStandard, endpointPkg, standardPkg⟩

end BEDC.Derived.RegularCauchyNameUp
