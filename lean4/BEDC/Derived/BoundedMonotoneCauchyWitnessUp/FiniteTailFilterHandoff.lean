import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_finite_tail_filter_handoff
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailWindow dyadicRead regularRead limitSeal realFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailWindow →
        Cont tailWindow ledger dyadicRead →
          Cont dyadicRead regular regularRead →
            Cont regularRead sealRow limitSeal →
              Cont limitSeal sealRow realFace →
                PkgSig bundle realFace pkg →
                  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                    UnaryHistory tailWindow ∧ UnaryHistory dyadicRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory limitSeal ∧
                        UnaryHistory realFace ∧ Cont source schedule tailWindow ∧
                          Cont tailWindow ledger dyadicRead ∧
                            Cont dyadicRead regular regularRead ∧
                              Cont regularRead sealRow limitSeal ∧
                                Cont limitSeal sealRow realFace ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier sourceScheduleTail tailLedgerDyadic dyadicRegularRead
    regularReadSealLimit limitSealReal realFacePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailWindowUnary : UnaryHistory tailWindow :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed tailWindowUnary ledgerUnary tailLedgerDyadic
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicReadUnary regularUnary dyadicRegularRead
  have limitSealUnary : UnaryHistory limitSeal :=
    unary_cont_closed regularReadUnary sealUnary regularReadSealLimit
  have realFaceUnary : UnaryHistory realFace :=
    unary_cont_closed limitSealUnary sealUnary limitSealReal
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, tailWindowUnary, dyadicReadUnary,
      regularReadUnary, limitSealUnary, realFaceUnary, sourceScheduleTail, tailLedgerDyadic,
      dyadicRegularRead, regularReadSealLimit, limitSealReal, provenancePkg, realFacePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
