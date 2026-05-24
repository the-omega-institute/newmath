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

theorem FiniteWindowRealSealAuditCarrier_nonescape [AskSetup] [PackageSetup]
    {window tolerance readback sealRow refusal transports routes provenance name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowRealSealAuditCarrier window tolerance readback sealRow refusal transports
        routes provenance name bundle pkg ->
      Cont sealRow name consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory window ∧ UnaryHistory tolerance ∧ UnaryHistory readback ∧
            UnaryHistory sealRow ∧ UnaryHistory refusal ∧ UnaryHistory consumer ∧
              Cont window tolerance readback ∧ Cont readback refusal sealRow ∧
                Cont sealRow name consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨windowUnary, toleranceUnary, readbackUnary, sealRowUnary, refusalUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, windowRoute,
    refusalSealRoute, provenancePkg, _namePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealRowUnary nameUnary consumerRoute
  exact
    ⟨windowUnary, toleranceUnary, readbackUnary, sealRowUnary, refusalUnary,
      consumerUnary, windowRoute, refusalSealRoute, consumerRoute, provenancePkg,
      consumerPkg⟩

theorem FiniteWindowRealSealAuditCarrier_transport_nonescape [AskSetup] [PackageSetup]
    {window tolerance readback sealRow refusal transports routes provenance name window'
      tolerance' readback' sealRow' refusal' transports' routes' provenance' name'
      consumer : BHist}
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
                                Cont sealRow' name' consumer →
                                  PkgSig bundle consumer pkg →
                                    UnaryHistory window' ∧ UnaryHistory tolerance' ∧
                                      UnaryHistory readback' ∧ UnaryHistory sealRow' ∧
                                        UnaryHistory refusal' ∧ UnaryHistory consumer ∧
                                          Cont window' tolerance' readback' ∧
                                            Cont readback' refusal' sealRow' ∧
                                              Cont sealRow' name' consumer ∧
                                                PkgSig bundle provenance' pkg ∧
                                                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameWindow sameTolerance sameReadback sameSealRow sameRefusal sameTransports
    sameRoutes sameProvenance sameName targetRoute targetRefusalSeal targetProvenancePkg
    targetNamePkg consumerRoute consumerPkg
  exact
    FiniteWindowRealSealAuditCarrier_nonescape
      (FiniteWindowRealSealAuditCarrier_refusal_transport carrier sameWindow sameTolerance
        sameReadback sameSealRow sameRefusal sameTransports sameRoutes sameProvenance sameName
        targetRoute targetRefusalSeal targetProvenancePkg targetNamePkg)
      consumerRoute consumerPkg

end BEDC.Derived.FiniteWindowRealSealAuditUp
