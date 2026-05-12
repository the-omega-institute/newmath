import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySubsequenceCarrier [AskSetup] [PackageSetup]
    (source reindex window radius sealRow xport route provenance cert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory reindex ∧ UnaryHistory window ∧
    UnaryHistory radius ∧ UnaryHistory sealRow ∧ UnaryHistory xport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        UnaryHistory endpoint ∧ Cont source reindex window ∧
          Cont window radius sealRow ∧ Cont sealRow xport route ∧
            Cont route provenance cert ∧ Cont cert endpoint endpoint ∧
              PkgSig bundle endpoint pkg

theorem RegularCauchySubsequenceCarrier_monotone_cofinal_window_transport
    [AskSetup] [PackageSetup]
    {source reindex window radius sealRow xport route provenance cert endpoint
      source' reindex' window' radius' sealRow' xport' route' provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubsequenceCarrier source reindex window radius sealRow xport route
        provenance cert endpoint bundle pkg ->
      hsame source source' ->
        hsame reindex reindex' ->
          Cont source' reindex' window' ->
            hsame radius radius' ->
              Cont window' radius' sealRow' ->
                hsame xport xport' ->
                  Cont sealRow' xport' route' ->
                    hsame provenance provenance' ->
                      hsame cert cert' ->
                        Cont route' provenance' cert' ->
                          Cont cert' endpoint endpoint ->
                            RegularCauchySubsequenceCarrier source' reindex' window'
                                radius' sealRow' xport' route' provenance' cert' endpoint
                                bundle pkg ∧
                              hsame window window' ∧ hsame sealRow sealRow' ∧
                                hsame route route' := by
  intro carrier sameSource sameReindex sourceRow' sameRadius windowRow' sameXport
    sealRowRoute' sameProvenance sameCert routeCert' certEndpoint'
  obtain ⟨sourceUnary, reindexUnary, windowUnary, radiusUnary, sealRowUnary,
    xportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary, sourceRow,
    windowRow, sealRowRoute, routeCert, _certEndpoint, pkgSig⟩ := carrier
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameSource sameReindex sourceRow sourceRow'
  have sameSealRow : hsame sealRow sealRow' :=
    cont_respects_hsame sameWindow sameRadius windowRow windowRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameSealRow sameXport sealRowRoute sealRowRoute'
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have reindexUnary' : UnaryHistory reindex' := unary_transport reindexUnary sameReindex
  have windowUnary' : UnaryHistory window' := unary_transport windowUnary sameWindow
  have radiusUnary' : UnaryHistory radius' := unary_transport radiusUnary sameRadius
  have sealRowUnary' : UnaryHistory sealRow' := unary_transport sealRowUnary sameSealRow
  have xportUnary' : UnaryHistory xport' := unary_transport xportUnary sameXport
  have routeUnary' : UnaryHistory route' := unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have certUnary' : UnaryHistory cert' := unary_transport certUnary sameCert
  exact
    ⟨⟨sourceUnary', reindexUnary', windowUnary', radiusUnary', sealRowUnary',
      xportUnary', routeUnary', provenanceUnary', certUnary', endpointUnary,
      sourceRow', windowRow', sealRowRoute', routeCert', certEndpoint', pkgSig⟩,
      sameWindow, sameSealRow, sameRoute⟩

end BEDC.Derived.RegularCauchySubsequenceUp
