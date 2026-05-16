import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_source_seal_totality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootRead sourceSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source regular rootRead →
        Cont rootRead sealRow sourceSealRead →
          PkgSig bundle sourceSealRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory rootRead ∧
                  UnaryHistory sourceSealRead ∧ Cont source regular rootRead ∧
                    Cont rootRead sealRow sourceSealRead ∧ Cont source schedule regular ∧
                      Cont regular witness trap ∧ Cont trap sealRow route ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle sourceSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceRegularRoot rootSealRead sourceSealPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  have sourceSealUnary : UnaryHistory sourceSealRead :=
    unary_cont_closed rootUnary sealUnary rootSealRead
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, rootUnary, sourceSealUnary, sourceRegularRoot, rootSealRead,
      sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg, sourceSealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
