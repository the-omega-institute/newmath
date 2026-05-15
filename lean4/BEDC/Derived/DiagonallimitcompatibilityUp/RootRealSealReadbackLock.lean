import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_real_seal_readback_lock [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      scheduledRead sealOut final : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows scheduledRead ->
        Cont scheduledRead realSeal sealOut ->
          Cont sealOut cert final ->
            PkgSig bundle final pkg ->
              UnaryHistory readback ∧ UnaryHistory scheduledRead ∧ UnaryHistory sealOut ∧
                UnaryHistory final ∧ hsame scheduledRead readback ∧
                  Cont scheduledRead realSeal sealOut ∧ Cont sealOut cert final ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle final pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier dyadicWindowsScheduled scheduledRealSealOut sealOutCertFinal finalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have scheduledUnary : UnaryHistory scheduledRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsScheduled
  have scheduledSameReadback : hsame scheduledRead readback :=
    cont_deterministic dyadicWindowsScheduled dyadicWindowsReadback
  have sealOutUnary : UnaryHistory sealOut :=
    unary_cont_closed scheduledUnary realSealUnary scheduledRealSealOut
  have finalUnary : UnaryHistory final :=
    unary_cont_closed sealOutUnary certUnary sealOutCertFinal
  exact
    ⟨readbackUnary, scheduledUnary, sealOutUnary, finalUnary, scheduledSameReadback,
      scheduledRealSealOut, sealOutCertFinal, provenancePkg, finalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
