import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_modulus_scope [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead scopedTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule tailRead ->
        Cont tailRead witness scopedTail ->
          PkgSig bundle scopedTail pkg ->
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
              UnaryHistory ledger ∧ UnaryHistory tailRead ∧ UnaryHistory scopedTail ∧
                Cont source schedule tailRead ∧ Cont tailRead witness scopedTail ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle scopedTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailWitnessScoped scopedTailPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have scopedTailUnary : UnaryHistory scopedTail :=
    unary_cont_closed tailUnary witnessUnary tailWitnessScoped
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, tailUnary, scopedTailUnary,
      sourceScheduleTail, tailWitnessScoped, provenancePkg, scopedTailPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
