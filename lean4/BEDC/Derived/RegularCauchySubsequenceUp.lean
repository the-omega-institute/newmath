import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySubsequenceCarrier [AskSetup] [PackageSetup]
    (source reindex window radius sealRow transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory reindex ∧ UnaryHistory window ∧
    UnaryHistory radius ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory nameCert ∧ Cont source reindex window ∧ Cont window radius transport ∧
        Cont transport route sealRow ∧ Cont sealRow provenance nameCert ∧
          PkgSig bundle provenance pkg

theorem RegularCauchySubsequenceCarrier_tail_classifier_stability [AskSetup] [PackageSetup]
    {source reindex window radius sealRow transport route nameCert source' reindex' window'
      radius' sealRow' transport' route' nameCert' provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubsequenceCarrier source reindex window radius sealRow transport route
        provenance nameCert bundle pkg ->
      hsame source source' ->
        hsame reindex reindex' ->
          hsame window window' ->
            hsame radius radius' ->
              hsame sealRow sealRow' ->
                hsame transport transport' ->
                  hsame route route' ->
                    hsame nameCert nameCert' ->
                      RegularCauchySubsequenceCarrier source' reindex' window' radius' sealRow'
                        transport' route' provenance nameCert' bundle pkg := by
  intro carrier sameSource sameReindex sameWindow sameRadius sameSeal sameTransport sameRoute
    sameNameCert
  obtain ⟨sourceUnary, reindexUnary, windowUnary, radiusUnary, sealUnary, transportUnary,
    routeUnary, nameCertUnary, sourceReindexWindow, windowRadiusTransport,
    transportRouteSeal, sealProvenanceNameCert, provenancePkg⟩ := carrier
  exact
    ⟨unary_transport sourceUnary sameSource,
      unary_transport reindexUnary sameReindex,
      unary_transport windowUnary sameWindow,
      unary_transport radiusUnary sameRadius,
      unary_transport sealUnary sameSeal,
      unary_transport transportUnary sameTransport,
      unary_transport routeUnary sameRoute,
      unary_transport nameCertUnary sameNameCert,
      cont_hsame_transport sameSource sameReindex sameWindow sourceReindexWindow,
      cont_hsame_transport sameWindow sameRadius sameTransport windowRadiusTransport,
      cont_hsame_transport sameTransport sameRoute sameSeal transportRouteSeal,
      cont_hsame_transport sameSeal (hsame_refl provenance) sameNameCert
        sealProvenanceNameCert,
      provenancePkg⟩

end BEDC.Derived.RegularCauchySubsequenceUp
