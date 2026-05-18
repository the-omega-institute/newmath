import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_selector_terminal_pullback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead readbackRead equalizedRead terminalRead diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule sourceRead ->
        Cont sourceRead regular readbackRead ->
          Cont source readbackRead equalizedRead ->
            Cont equalizedRead sealRow terminalRead ->
              Cont terminalRead provenance diagonalRead ->
                PkgSig bundle diagonalRead pkg ->
                  UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                    UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory sourceRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory equalizedRead ∧
                        UnaryHistory terminalRead ∧ UnaryHistory diagonalRead ∧
                          Cont source schedule sourceRead ∧
                            Cont sourceRead regular readbackRead ∧
                              Cont source readbackRead equalizedRead ∧
                                Cont equalizedRead sealRow terminalRead ∧
                                  Cont terminalRead provenance diagonalRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRead readbackStep equalizerStep terminalStep diagonalStep
    diagonalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed sourceReadUnary regularUnary readbackStep
  have equalizedUnary : UnaryHistory equalizedRead :=
    unary_cont_closed sourceUnary readbackUnary equalizerStep
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed equalizedUnary sealUnary terminalStep
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed terminalUnary provenanceUnary diagonalStep
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, sealUnary, provenanceUnary, sourceReadUnary,
      readbackUnary, equalizedUnary, terminalUnary, diagonalUnary, sourceScheduleRead,
      readbackStep, equalizerStep, terminalStep, diagonalStep, provenancePkg, diagonalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
