import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_cauchycriterion_selector_handoff
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      criterionBudget criterionTail criterionWindow criterionSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont regular witness trap ->
        Cont trap sealRow route ->
          Cont criterionBudget criterionTail criterionWindow ->
            Cont criterionWindow sealRow criterionSeal ->
              hsame criterionSeal sealRow ->
                PkgSig bundle provenance pkg ->
                  UnaryHistory trap ∧ UnaryHistory route ∧ Cont regular witness trap ∧
                    Cont trap sealRow route ∧
                      Cont criterionBudget criterionTail criterionWindow ∧
                        Cont criterionWindow sealRow criterionSeal ∧
                          hsame criterionSeal sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _regularWitnessTrap _trapSealRoute criterionWindowRoute criterionSealRoute
    sameSeal _provenancePkg
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary,
    trapUnary, sealUnary, _provenanceUnary, _sourceScheduleRegular,
    carrierRegularWitnessTrap, carrierTrapSealRoute, _transportLocalCertRoute,
    _routeProvenanceSeal, carrierProvenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary carrierTrapSealRoute
  exact
    ⟨trapUnary, routeUnary, carrierRegularWitnessTrap, carrierTrapSealRoute,
      criterionWindowRoute, criterionSealRoute, sameSeal, carrierProvenancePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
