import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_modulus_ledger_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRequest dyadicRead locatedRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont witness schedule tailRequest →
        Cont tailRequest ledger dyadicRead →
          Cont dyadicRead trap locatedRead →
            Cont locatedRead sealRow realRead →
              PkgSig bundle realRead pkg →
                UnaryHistory witness ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                  UnaryHistory tailRequest ∧ UnaryHistory dyadicRead ∧
                    UnaryHistory locatedRead ∧ UnaryHistory realRead ∧
                      Cont witness schedule tailRequest ∧ Cont tailRequest ledger dyadicRead ∧
                        Cont dyadicRead trap locatedRead ∧ Cont locatedRead sealRow realRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier witnessScheduleTail tailLedgerDyadic dyadicTrapLocated locatedSealReal realPkg
  obtain ⟨_sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have tailUnary : UnaryHistory tailRequest :=
    unary_cont_closed witnessUnary scheduleUnary witnessScheduleTail
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerDyadic
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed dyadicUnary trapUnary dyadicTrapLocated
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed locatedUnary sealUnary locatedSealReal
  exact
    ⟨witnessUnary, scheduleUnary, ledgerUnary, tailUnary, dyadicUnary, locatedUnary, realUnary,
      witnessScheduleTail, tailLedgerDyadic, dyadicTrapLocated, locatedSealReal, provenancePkg,
      realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
