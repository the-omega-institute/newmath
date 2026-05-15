import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_tail_modulus_ledger
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRequest dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont witness schedule tailRequest ->
        Cont tailRequest ledger dyadicRead ->
          PkgSig bundle dyadicRead pkg ->
            UnaryHistory witness ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
              UnaryHistory tailRequest ∧ UnaryHistory dyadicRead ∧
                Cont witness schedule tailRequest ∧ Cont tailRequest ledger dyadicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle dyadicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier witnessScheduleTail tailLedgerDyadic dyadicPkg
  obtain ⟨_sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have tailUnary : UnaryHistory tailRequest :=
    unary_cont_closed witnessUnary scheduleUnary witnessScheduleTail
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerDyadic
  exact
    ⟨witnessUnary, scheduleUnary, ledgerUnary, tailUnary, dyadicUnary, witnessScheduleTail,
      tailLedgerDyadic, provenancePkg, dyadicPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
