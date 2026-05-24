import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_bounded_tail_ledger_factorization [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      boundedWindow boundedLedger jointTail boundedTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory boundedWindow ->
        UnaryHistory boundedLedger ->
          Cont sealRow boundedWindow jointTail ->
            Cont jointTail boundedLedger boundedTail ->
              PkgSig bundle boundedTail pkg ->
                UnaryHistory sealRow ∧ UnaryHistory boundedWindow ∧
                  UnaryHistory boundedLedger ∧ UnaryHistory jointTail ∧
                    UnaryHistory boundedTail ∧ Cont modulus windows dyadic ∧
                      Cont dyadic readback sealRow ∧ Cont sealRow boundedWindow jointTail ∧
                        Cont jointTail boundedLedger boundedTail ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle boundedTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier boundedWindowUnary boundedLedgerUnary sealWindowTail tailLedgerBounded
    boundedTailPkg
  obtain ⟨_modulusUnary, _windowsUnary, _dyadicUnary, _readbackUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have jointTailUnary : UnaryHistory jointTail :=
    unary_cont_closed sealUnary boundedWindowUnary sealWindowTail
  have boundedTailUnary : UnaryHistory boundedTail :=
    unary_cont_closed jointTailUnary boundedLedgerUnary tailLedgerBounded
  exact
    ⟨sealUnary, boundedWindowUnary, boundedLedgerUnary, jointTailUnary, boundedTailUnary,
      modulusWindowRoute, dyadicReadbackRoute, sealWindowTail, tailLedgerBounded,
      provenancePkg, boundedTailPkg⟩

end BEDC.Derived.RealCauchyModulusUp
