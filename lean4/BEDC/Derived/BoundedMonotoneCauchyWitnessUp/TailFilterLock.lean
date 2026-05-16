import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_filter_lock [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailWindow dyadicRead regularRead limitSeal realFace windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule tailWindow ->
        Cont tailWindow ledger dyadicRead ->
          Cont dyadicRead regular regularRead ->
            Cont regularRead sealRow limitSeal ->
              Cont limitSeal sealRow realFace ->
                Cont tailWindow regular windowRead ->
                  Cont windowRead sealRow sealRead ->
                    PkgSig bundle realFace pkg ->
                      PkgSig bundle sealRead pkg ->
                        UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                          UnaryHistory tailWindow ∧ UnaryHistory dyadicRead ∧
                            UnaryHistory regularRead ∧ UnaryHistory limitSeal ∧
                              UnaryHistory realFace ∧ UnaryHistory windowRead ∧
                                UnaryHistory sealRead ∧ Cont source schedule tailWindow ∧
                                  Cont tailWindow ledger dyadicRead ∧
                                    Cont dyadicRead regular regularRead ∧
                                      Cont regularRead sealRow limitSeal ∧
                                        Cont limitSeal sealRow realFace ∧
                                          Cont tailWindow regular windowRead ∧
                                            Cont windowRead sealRow sealRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle realFace pkg ∧
                                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailLedgerDyadic dyadicRegularRead
    regularReadSealLimit limitSealReal tailRegularWindow windowSealRead realFacePkg
    sealReadPkg
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
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed tailWindowUnary regularUnary tailRegularWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnary windowSealRead
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, tailWindowUnary, dyadicReadUnary,
      regularReadUnary, limitSealUnary, realFaceUnary, windowReadUnary, sealReadUnary,
      sourceScheduleTail, tailLedgerDyadic, dyadicRegularRead, regularReadSealLimit,
      limitSealReal, tailRegularWindow, windowSealRead, provenancePkg, realFacePkg,
      sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
