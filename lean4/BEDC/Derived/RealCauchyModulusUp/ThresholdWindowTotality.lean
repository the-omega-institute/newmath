import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_threshold_window_totality [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      precision threshold window : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes
        provenance localCert bundle pkg →
      UnaryHistory precision →
        Cont precision modulus threshold →
          Cont threshold windows window →
            PkgSig bundle window pkg →
              UnaryHistory threshold ∧ UnaryHistory window ∧
                Cont precision modulus threshold ∧ Cont threshold windows window ∧
                  Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle window pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier precisionUnary thresholdCont windowCont windowPkg
  obtain ⟨modulusUnary, windowsUnary, _dyadicUnary, _readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed precisionUnary modulusUnary thresholdCont
  have windowUnary : UnaryHistory window :=
    unary_cont_closed thresholdUnary windowsUnary windowCont
  exact
    ⟨thresholdUnary, windowUnary, thresholdCont, windowCont, modulusWindowRoute,
      dyadicReadbackRoute, provenancePkg, windowPkg⟩

theorem RealCauchyModulusCarrier_seal_determinacy [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      modulus' windows' dyadic' readback' sealRow' transports' routes' provenance' localCert'
      consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes
        provenance localCert bundle pkg →
      RealCauchyModulusCarrier modulus' windows' dyadic' readback' sealRow' transports'
        routes' provenance' localCert' bundle pkg →
        hsame sealRow sealRow' →
          hsame routes routes' →
            Cont sealRow routes consumer →
              Cont sealRow' routes' consumer' →
                PkgSig bundle consumer pkg →
                  PkgSig bundle consumer' pkg →
                    hsame consumer consumer' ∧ UnaryHistory consumer ∧ UnaryHistory consumer' ∧
                      Cont sealRow routes consumer ∧ Cont sealRow' routes' consumer' ∧
                        PkgSig bundle consumer pkg ∧ PkgSig bundle consumer' pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier carrier' sameSeal sameRoutes consumerCont consumerCont' consumerPkg consumerPkg'
  obtain ⟨_modulusUnary, _windowsUnary, _dyadicUnary, _readbackUnary, sealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, _modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, _provenancePkg, _localSemantic⟩ := carrier
  obtain ⟨_modulusUnary', _windowsUnary', _dyadicUnary', _readbackUnary', sealUnary',
    _transportsUnary', routesUnary', _provenanceUnary', _localCertUnary',
      _modulusWindowRoute', _dyadicReadbackRoute', _sealRoute', _provenancePkg',
        _localSemantic'⟩ := carrier'
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary routesUnary consumerCont
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed sealUnary' routesUnary' consumerCont'
  cases sameSeal
  cases sameRoutes
  cases consumerCont
  cases consumerCont'
  exact
    ⟨rfl, consumerUnary, consumerUnary', rfl, rfl, consumerPkg, consumerPkg'⟩

end BEDC.Derived.RealCauchyModulusUp
