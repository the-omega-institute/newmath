import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_route_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow provenance convergenceRead ->
        PkgSig bundle convergenceRead pkg ->
          UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
            UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
              UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory convergenceRead ∧
                Cont source schedule regular ∧ Cont regular witness trap ∧
                  Cont trap sealRow route ∧ Cont sealRow provenance convergenceRead ∧
                    Cont transport localCert route ∧ Cont route provenance sealRow ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier convergenceRoute convergencePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary convergenceRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, convergenceUnary, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, convergenceRoute, transportLocalCertRoute, routeProvenanceSeal,
      provenancePkg, convergencePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
