import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_selector_synchronization
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      selectedTail selectorSeal convergenceSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont witness schedule selectedTail ->
        Cont selectedTail trap selectorSeal ->
          Cont selectorSeal sealRow convergenceSeal ->
            PkgSig bundle convergenceSeal pkg ->
              UnaryHistory witness ∧ UnaryHistory schedule ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory selectedTail ∧
                  UnaryHistory selectorSeal ∧ UnaryHistory convergenceSeal ∧
                    Cont witness schedule selectedTail ∧ Cont selectedTail trap selectorSeal ∧
                      Cont selectorSeal sealRow convergenceSeal ∧ Cont source schedule regular ∧
                        Cont regular witness trap ∧ Cont trap sealRow route ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle convergenceSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier witnessScheduleTail tailTrapSelector selectorSealRoute convergencePkg
  obtain ⟨_sourceUnary, regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have selectedTailUnary : UnaryHistory selectedTail :=
    unary_cont_closed witnessUnary scheduleUnary witnessScheduleTail
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectedTailUnary trapUnary tailTrapSelector
  have convergenceSealUnary : UnaryHistory convergenceSeal :=
    unary_cont_closed selectorSealUnary sealUnary selectorSealRoute
  exact
    ⟨witnessUnary, scheduleUnary, trapUnary, sealUnary, selectedTailUnary, selectorSealUnary,
      convergenceSealUnary, witnessScheduleTail, tailTrapSelector, selectorSealRoute,
      sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg, convergencePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
