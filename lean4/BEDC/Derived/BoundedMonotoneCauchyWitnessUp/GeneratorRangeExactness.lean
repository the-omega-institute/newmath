import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_generator_range_exactness
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert generatorRead upperRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source regular generatorRead →
        Cont generatorRead ledger upperRead →
          PkgSig bundle upperRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory ledger ∧
              UnaryHistory generatorRead ∧ UnaryHistory upperRead ∧
                Cont source regular generatorRead ∧ Cont generatorRead ledger upperRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle upperRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceRegularGenerator generatorLedgerUpper upperPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have generatorUnary : UnaryHistory generatorRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularGenerator
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed generatorUnary ledgerUnary generatorLedgerUpper
  exact
    ⟨sourceUnary, regularUnary, ledgerUnary, generatorUnary, upperUnary,
      sourceRegularGenerator, generatorLedgerUpper, provenancePkg, upperPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
