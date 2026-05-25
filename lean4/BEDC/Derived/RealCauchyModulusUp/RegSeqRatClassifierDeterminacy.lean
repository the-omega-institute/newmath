import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_regseqrat_classifier_determinacy [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert modulus'
      windows' dyadic' readback' sealRow' transports' routes' provenance' localCert'
      terminal terminal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes
        provenance localCert bundle pkg →
      RealCauchyModulusCarrier modulus' windows' dyadic' readback' sealRow' transports'
        routes' provenance' localCert' bundle pkg →
        hsame dyadic dyadic' →
          hsame readback readback' →
            hsame sealRow sealRow' →
              hsame routes routes' →
                Cont dyadic readback sealRow →
                  Cont dyadic' readback' sealRow' →
                    Cont readback sealRow terminal →
                      Cont readback' sealRow' terminal' →
                        PkgSig bundle terminal pkg →
                          PkgSig bundle terminal' pkg →
                            hsame terminal terminal' ∧ UnaryHistory readback ∧
                              UnaryHistory readback' ∧ UnaryHistory sealRow ∧
                                UnaryHistory sealRow' ∧ UnaryHistory terminal ∧
                                  UnaryHistory terminal' ∧ Cont dyadic readback sealRow ∧
                                    Cont dyadic' readback' sealRow' ∧
                                      Cont readback sealRow terminal ∧
                                        Cont readback' sealRow' terminal' ∧
                                          PkgSig bundle terminal pkg ∧
                                            PkgSig bundle terminal' pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier carrier' _sameDyadic sameReadback sameSeal _sameRoutes dyadicReadbackCont
    dyadicReadbackCont' terminalCont terminalCont' terminalPkg terminalPkg'
  obtain ⟨_modulusUnary, _windowsUnary, _dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, _provenancePkg, _localSemantic⟩ := carrier
  obtain ⟨_modulusUnary', _windowsUnary', _dyadicUnary', readbackUnary', sealUnary',
    _transportsUnary', _routesUnary', _provenanceUnary', _localCertUnary',
      _modulusWindowRoute', _dyadicReadbackRoute', _sealRoute', _provenancePkg',
        _localSemantic'⟩ := carrier'
  have terminalSame : hsame terminal terminal' :=
    cont_respects_hsame sameReadback sameSeal terminalCont terminalCont'
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary sealUnary terminalCont
  have terminalUnary' : UnaryHistory terminal' :=
    unary_cont_closed readbackUnary' sealUnary' terminalCont'
  exact
    ⟨terminalSame, readbackUnary, readbackUnary', sealUnary, sealUnary', terminalUnary,
      terminalUnary', dyadicReadbackCont, dyadicReadbackCont', terminalCont, terminalCont',
      terminalPkg, terminalPkg'⟩

end BEDC.Derived.RealCauchyModulusUp
