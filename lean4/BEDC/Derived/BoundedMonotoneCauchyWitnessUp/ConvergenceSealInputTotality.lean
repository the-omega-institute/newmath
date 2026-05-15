import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_input_totality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceInput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule convergenceInput ->
        Cont convergenceInput sealRow route ->
          PkgSig bundle convergenceInput pkg ->
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory convergenceInput ∧
              UnaryHistory sealRow ∧ UnaryHistory route ∧
                Cont source schedule convergenceInput ∧
                  Cont convergenceInput sealRow route ∧ Cont route provenance sealRow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle convergenceInput pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle
  intro carrier sourceScheduleConvergence convergenceSealRoute convergencePkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary,
    _trapUnary, sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have convergenceUnary : UnaryHistory convergenceInput :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleConvergence
  have routeUnary : UnaryHistory route :=
    unary_cont_closed convergenceUnary sealUnary convergenceSealRoute
  exact
    ⟨sourceUnary, scheduleUnary, convergenceUnary, sealUnary, routeUnary,
      sourceScheduleConvergence, convergenceSealRoute, routeProvenanceSeal, provenancePkg,
      convergencePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
