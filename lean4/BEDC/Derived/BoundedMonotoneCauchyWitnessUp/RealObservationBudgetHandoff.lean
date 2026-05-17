import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_observation_budget_handoff
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      observationRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont schedule ledger observationRead →
        Cont observationRead regular sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory ledger ∧ UnaryHistory observationRead ∧ UnaryHistory sealRead ∧
                Cont schedule ledger observationRead ∧
                  Cont observationRead regular sealRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier scheduleLedgerObservation observationRegularSeal sealPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerObservation
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed observationUnary regularUnary observationRegularSeal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, ledgerUnary, observationUnary, sealReadUnary,
      scheduleLedgerObservation, observationRegularSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
