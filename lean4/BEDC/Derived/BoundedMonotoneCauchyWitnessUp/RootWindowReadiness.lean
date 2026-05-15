import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_window_readiness [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead sealRead suffixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule windowRead ->
        Cont windowRead witness sealRead ->
          Cont sealRead sealRow suffixRead ->
            PkgSig bundle suffixRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory suffixRead ∧ Cont source schedule windowRead ∧
                      Cont windowRead witness sealRead ∧ Cont sealRead sealRow suffixRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle suffixRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessSeal sealSealSuffix suffixPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessSeal
  have suffixUnary : UnaryHistory suffixRead :=
    unary_cont_closed sealReadUnary sealUnary sealSealSuffix
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      windowUnary, sealReadUnary, suffixUnary, sourceScheduleWindow, windowWitnessSeal,
      sealSealSuffix, provenancePkg, suffixPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
