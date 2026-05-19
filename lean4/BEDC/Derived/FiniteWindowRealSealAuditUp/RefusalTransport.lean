import BEDC.Derived.FiniteWindowRealSealAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowRealSealAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteWindowRealSealAuditCarrier [AskSetup] [PackageSetup]
    (window tolerance readback sealRow refusal transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧
    UnaryHistory tolerance ∧
      UnaryHistory readback ∧
        UnaryHistory sealRow ∧
          UnaryHistory refusal ∧
            UnaryHistory transports ∧
              UnaryHistory routes ∧
                UnaryHistory provenance ∧
                  UnaryHistory name ∧
                    Cont window tolerance readback ∧
                      Cont readback refusal sealRow ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle name pkg

theorem FiniteWindowRealSealAuditCarrier_refusal_transport [AskSetup] [PackageSetup]
    {window tolerance readback sealRow refusal transports routes provenance name window'
      tolerance' readback' sealRow' refusal' transports' routes' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowRealSealAuditCarrier window tolerance readback sealRow refusal transports
        routes provenance name bundle pkg →
      hsame window window' →
        hsame tolerance tolerance' →
          hsame readback readback' →
            hsame sealRow sealRow' →
              hsame refusal refusal' →
                hsame transports transports' →
                  hsame routes routes' →
                    hsame provenance provenance' →
                      hsame name name' →
                        Cont window' tolerance' readback' →
                          Cont readback' refusal' sealRow' →
                            PkgSig bundle provenance' pkg →
                              PkgSig bundle name' pkg →
                                FiniteWindowRealSealAuditCarrier window' tolerance'
                                  readback' sealRow' refusal' transports' routes' provenance'
                                  name' bundle pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameWindow sameTolerance sameReadback sameSealRow sameRefusal sameTransports
    sameRoutes sameProvenance sameName targetRoute targetRefusalSeal targetProvenancePkg
    targetNamePkg
  obtain ⟨windowUnary, toleranceUnary, readbackUnary, sealRowUnary, refusalUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, _sourceRoute,
    _sourceRefusalSeal, _sourceProvenancePkg, _sourceNamePkg⟩ := carrier
  exact
    ⟨unary_transport windowUnary sameWindow,
      unary_transport toleranceUnary sameTolerance,
      unary_transport readbackUnary sameReadback,
      unary_transport sealRowUnary sameSealRow,
      unary_transport refusalUnary sameRefusal,
      unary_transport transportsUnary sameTransports,
      unary_transport routesUnary sameRoutes,
      unary_transport provenanceUnary sameProvenance,
      unary_transport nameUnary sameName,
      targetRoute,
      targetRefusalSeal,
      targetProvenancePkg,
      targetNamePkg⟩

end BEDC.Derived.FiniteWindowRealSealAuditUp
