import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_source_readback_equalizer
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead readbackRead equalizedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule sourceRead →
        Cont sourceRead regular readbackRead →
          Cont source readbackRead equalizedRead →
            PkgSig bundle equalizedRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory sourceRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory equalizedRead ∧ Cont source schedule sourceRead ∧
                    Cont sourceRead regular readbackRead ∧
                      Cont source readbackRead equalizedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle equalizedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRead sourceReadRegularReadback sourceReadbackEqualized
    equalizedPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
      carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed sourceReadUnary regularUnary sourceReadRegularReadback
  have equalizedReadUnary : UnaryHistory equalizedRead :=
    unary_cont_closed sourceUnary readbackReadUnary sourceReadbackEqualized
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, sourceReadUnary, readbackReadUnary,
      equalizedReadUnary, sourceScheduleRead, sourceReadRegularReadback, sourceReadbackEqualized,
      provenancePkg, equalizedPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
