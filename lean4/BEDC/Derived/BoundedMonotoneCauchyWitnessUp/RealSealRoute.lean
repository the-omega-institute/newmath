import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_route
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont trap sealRow route →
        Cont route provenance realRead →
          PkgSig bundle realRead pkg →
            UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory realRead ∧ Cont trap sealRow route ∧
                Cont route provenance realRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier trapSealRoute routeProvenanceReal realPkg
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _carrierTrapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal,
    provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceReal
  exact
    ⟨trapUnary, sealUnary, routeUnary, provenanceUnary, realUnary, trapSealRoute,
      routeProvenanceReal, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
