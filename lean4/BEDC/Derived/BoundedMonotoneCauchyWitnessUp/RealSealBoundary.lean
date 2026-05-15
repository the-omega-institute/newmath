import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_boundary
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      preSealRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont trap sealRow preSealRead →
        Cont preSealRead provenance realSealRead →
          PkgSig bundle realSealRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory preSealRead ∧
                  UnaryHistory realSealRead ∧ Cont trap sealRow route ∧
                    Cont trap sealRow preSealRead ∧
                      Cont preSealRead provenance realSealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier trapSealPre realSealRoute realSealPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have preSealUnary : UnaryHistory preSealRead :=
    unary_cont_closed trapUnary sealUnary trapSealPre
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed preSealUnary provenanceUnary realSealRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, preSealUnary, realSealUnary, trapSealRoute, trapSealPre, realSealRoute,
      provenancePkg, realSealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
