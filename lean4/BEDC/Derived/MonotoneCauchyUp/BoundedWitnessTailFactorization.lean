import BEDC.Derived.MonotoneCauchyUp
import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_bounded_witness_tail_factorization [AskSetup]
    [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      source witness trap boundedSeal boundedTransport boundedRoute boundedProvenance
      boundedLocal commonWindow boundedTailRead boundedPublicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      BEDC.Derived.BoundedMonotoneCauchyWitnessUp.BoundedMonotoneCauchyWitnessCarrier
        source regular schedule witness ledger trap boundedSeal boundedTransport boundedRoute
        boundedProvenance boundedLocal bundle pkg ->
        Cont schedule modulus commonWindow ->
          Cont commonWindow witness boundedTailRead ->
            Cont boundedTailRead realSeal boundedPublicRead ->
              PkgSig bundle boundedPublicRead pkg ->
                UnaryHistory commonWindow ∧ UnaryHistory boundedTailRead ∧
                  UnaryHistory boundedPublicRead ∧ Cont schedule modulus commonWindow ∧
                    Cont commonWindow witness boundedTailRead ∧
                      Cont boundedTailRead realSeal boundedPublicRead ∧
                        Cont modulus ledger interval ∧ Cont interval realSeal nameRow ∧
                          PkgSig bundle nameRow pkg ∧
                            PkgSig bundle boundedPublicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier bounded scheduleModulusCommon commonWitnessTail tailSealPublic publicPkg
  obtain ⟨_regularUnary, scheduleUnary, modulusUnary, _ledgerUnary, _intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  obtain ⟨_sourceUnary, _regularUnaryB, _scheduleUnaryB, witnessUnary, _ledgerUnaryB,
    _trapUnary, _boundedSealUnary, _boundedProvenanceUnary, _sourceScheduleRegular,
    _regularWitnessTrap, _trapSealRoute, _transportLocalRoute, _routeProvenanceSeal,
    _boundedProvenancePkg⟩ := bounded
  have commonUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommon
  have tailUnary : UnaryHistory boundedTailRead :=
    unary_cont_closed commonUnary witnessUnary commonWitnessTail
  have publicUnary : UnaryHistory boundedPublicRead :=
    unary_cont_closed tailUnary realSealUnary tailSealPublic
  exact
    ⟨commonUnary, tailUnary, publicUnary, scheduleModulusCommon, commonWitnessTail,
      tailSealPublic, modulusLedgerInterval, intervalRealSealNameRow, nameRowPkg, publicPkg⟩

end BEDC.Derived.MonotoneCauchyUp
