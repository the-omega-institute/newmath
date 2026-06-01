import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_located_metric_readiness [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName locatedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg →
      Cont distance stream locatedRead →
        PkgSig bundle locatedRead pkg →
          UnaryHistory locatedRead ∧ Cont stream readback dyadic ∧
            Cont dyadic sealRow zeroRow ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle locatedRead pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier locatedRoute locatedPkg
  obtain ⟨_pointUnary, distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    _sealUnary, _zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed distanceUnary streamUnary locatedRoute
  exact ⟨locatedUnary, streamReadbackDyadic, dyadicSealZero, localNamePkg, locatedPkg⟩

end BEDC.Derived.PseudometricUp
