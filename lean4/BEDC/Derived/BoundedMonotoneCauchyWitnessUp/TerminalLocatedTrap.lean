import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_terminal_located_trap_preservation
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      locatedRead locatedRead' toleranceRead toleranceRead' realRead realRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont trap ledger locatedRead ->
        Cont trap ledger locatedRead' ->
          Cont locatedRead witness toleranceRead ->
            Cont locatedRead' witness toleranceRead' ->
              Cont toleranceRead sealRow realRead ->
                Cont toleranceRead' sealRow realRead' ->
                  PkgSig bundle realRead pkg ->
                    PkgSig bundle realRead' pkg ->
                      UnaryHistory locatedRead /\ UnaryHistory locatedRead' /\
                        UnaryHistory toleranceRead /\ UnaryHistory toleranceRead' /\
                          UnaryHistory realRead /\ UnaryHistory realRead' /\
                            hsame locatedRead locatedRead' /\
                              hsame toleranceRead toleranceRead' /\ hsame realRead realRead' /\
                                Cont trap ledger locatedRead /\
                                  Cont trap ledger locatedRead' /\
                                    Cont locatedRead witness toleranceRead /\
                                      Cont locatedRead' witness toleranceRead' /\
                                        Cont toleranceRead sealRow realRead /\
                                          Cont toleranceRead' sealRow realRead' /\
                                            PkgSig bundle provenance pkg /\
                                              PkgSig bundle realRead pkg /\
                                                PkgSig bundle realRead' pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier trapLedgerLocated trapLedgerLocated' locatedWitnessTolerance
    locatedWitnessTolerance' toleranceSealReal toleranceSealReal' realPkg realPkg'
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed trapUnary ledgerUnary trapLedgerLocated
  have locatedUnary' : UnaryHistory locatedRead' :=
    unary_cont_closed trapUnary ledgerUnary trapLedgerLocated'
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed locatedUnary witnessUnary locatedWitnessTolerance
  have toleranceUnary' : UnaryHistory toleranceRead' :=
    unary_cont_closed locatedUnary' witnessUnary locatedWitnessTolerance'
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed toleranceUnary sealUnary toleranceSealReal
  have realUnary' : UnaryHistory realRead' :=
    unary_cont_closed toleranceUnary' sealUnary toleranceSealReal'
  have locatedSame : hsame locatedRead locatedRead' :=
    cont_respects_hsame (hsame_refl trap) (hsame_refl ledger) trapLedgerLocated
      trapLedgerLocated'
  have toleranceSame : hsame toleranceRead toleranceRead' :=
    cont_respects_hsame locatedSame (hsame_refl witness) locatedWitnessTolerance
      locatedWitnessTolerance'
  have realSame : hsame realRead realRead' :=
    cont_respects_hsame toleranceSame (hsame_refl sealRow) toleranceSealReal
      toleranceSealReal'
  exact
    ⟨locatedUnary, locatedUnary', toleranceUnary, toleranceUnary', realUnary, realUnary',
      locatedSame, toleranceSame, realSame, trapLedgerLocated, trapLedgerLocated',
      locatedWitnessTolerance, locatedWitnessTolerance', toleranceSealReal,
      toleranceSealReal', provenancePkg, realPkg, realPkg'⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
