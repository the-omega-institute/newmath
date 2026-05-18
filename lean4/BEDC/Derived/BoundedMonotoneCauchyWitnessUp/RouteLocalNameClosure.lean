import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_route_local_name_closure
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      UnaryHistory localCert ∧ Cont transport localCert route ∧
        Cont route provenance sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary,
    _trapUnary, _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    trapSealRoute, transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed _trapUnary _sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalCertRoute routeUnary).right
  exact ⟨localCertUnary, transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
