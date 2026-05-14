import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_window_lock [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead regular windowRead →
          Cont windowRead sealRow sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory tailRead ∧ UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                  Cont source schedule tailRead ∧ Cont tailRead regular windowRead ∧
                    Cont windowRead sealRow sealRead ∧ Cont source schedule regular ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailRegularWindow windowSealRead sealReadPkg
  rcases carrier with
    ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
      sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap,
      _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tailUnary regularUnary tailRegularWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary sealUnary windowSealRead
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, tailUnary, windowUnary, sealReadUnary,
      sourceScheduleTail, tailRegularWindow, windowSealRead, sourceScheduleRegular,
      provenancePkg, sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
