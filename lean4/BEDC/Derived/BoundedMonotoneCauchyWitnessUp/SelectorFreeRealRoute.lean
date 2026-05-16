import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_selector_free_real_route [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      selectorRead tailRead criterionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule selectorRead ->
        Cont selectorRead regular tailRead ->
          Cont tailRead witness criterionRead ->
            Cont criterionRead sealRow realRead ->
              PkgSig bundle realRead pkg ->
                UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                  UnaryHistory witness ∧ UnaryHistory sealRow ∧ UnaryHistory selectorRead ∧
                    UnaryHistory tailRead ∧ UnaryHistory criterionRead ∧
                      UnaryHistory realRead ∧ Cont source schedule selectorRead ∧
                        Cont selectorRead regular tailRead ∧
                          Cont tailRead witness criterionRead ∧
                            Cont criterionRead sealRow realRead ∧
                              Cont source schedule regular ∧ Cont regular witness trap ∧
                                Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleSelector selectorRegularTail tailWitnessCriterion
    criterionSealReal realPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleSelector
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed selectorUnary regularUnary selectorRegularTail
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessCriterion
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealReal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, sealUnary, selectorUnary,
      tailUnary, criterionUnary, realUnary, sourceScheduleSelector, selectorRegularTail,
      tailWitnessCriterion, criterionSealReal, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
