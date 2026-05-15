import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_ledger_exhaustion [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont route provenance publicRead →
        PkgSig bundle publicRead pkg →
          UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
            UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
              UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory publicRead ∧
                Cont source schedule regular ∧ Cont regular witness trap ∧
                  Cont trap sealRow route ∧ Cont route provenance sealRow ∧
                    Cont route provenance publicRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier routePublic publicPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary routePublic
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, publicUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      routeProvenanceSeal, routePublic, provenancePkg, publicPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
