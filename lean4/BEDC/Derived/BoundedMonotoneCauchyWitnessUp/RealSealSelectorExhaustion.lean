import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_selector_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      selectorPrefix sealSuffix selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule selectorPrefix →
        Cont trap sealRow sealSuffix →
          Cont selectorPrefix sealSuffix selectorRead →
            PkgSig bundle selectorRead pkg →
              UnaryHistory selectorPrefix ∧ UnaryHistory sealSuffix ∧
                UnaryHistory selectorRead ∧ Cont source schedule selectorPrefix ∧
                  Cont trap sealRow sealSuffix ∧ Cont selectorPrefix sealSuffix selectorRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleSelector trapSealSuffix selectorSuffixRead selectorPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have selectorPrefixUnary : UnaryHistory selectorPrefix :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleSelector
  have sealSuffixUnary : UnaryHistory sealSuffix :=
    unary_cont_closed trapUnary sealUnary trapSealSuffix
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed selectorPrefixUnary sealSuffixUnary selectorSuffixRead
  exact
    ⟨selectorPrefixUnary, sealSuffixUnary, selectorReadUnary, sourceScheduleSelector,
      trapSealSuffix, selectorSuffixRead, provenancePkg, selectorPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
