import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySubsequenceCarrier [AskSetup] [PackageSetup]
    (source reindex windows radius «seal» sameRows routeRows provenance localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory reindex ∧ UnaryHistory windows ∧ UnaryHistory radius ∧
    UnaryHistory «seal» ∧ UnaryHistory sameRows ∧ UnaryHistory routeRows ∧
      UnaryHistory provenance ∧ UnaryHistory localCert ∧ UnaryHistory endpoint ∧
        Cont source reindex windows ∧ Cont windows radius «seal» ∧
          Cont sameRows routeRows provenance ∧ Cont provenance localCert endpoint ∧
            hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg

theorem RegularCauchySubsequenceCarrier_monotone_cofinal_window_transport
    [AskSetup] [PackageSetup]
    {source reindex windows radius «seal» sameRows routeRows provenance localCert endpoint
      source' reindex' windows' radius' seal' sameRows' routeRows' provenance' localCert'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubsequenceCarrier source reindex windows radius «seal» sameRows routeRows
        provenance localCert endpoint bundle pkg ->
      hsame source source' ->
        hsame reindex reindex' ->
          Cont source' reindex' windows' ->
            hsame radius radius' ->
              Cont windows' radius' seal' ->
                hsame sameRows sameRows' ->
                  hsame routeRows routeRows' ->
                    Cont sameRows' routeRows' provenance' ->
                      hsame localCert localCert' ->
                        Cont provenance' localCert' endpoint' ->
                          hsame endpoint' (append provenance' localCert') ->
                            PkgSig bundle endpoint' pkg ->
                              RegularCauchySubsequenceCarrier source' reindex' windows'
                                  radius' seal' sameRows' routeRows' provenance' localCert'
                                  endpoint' bundle pkg ∧
                                hsame windows windows' ∧ hsame «seal» seal' ∧
                                  hsame provenance provenance' := by
  intro carrier sameSource sameReindex sourceReindexWindows' sameRadius windowsRadiusSeal'
    sameSameRows sameRouteRows sameRowsRouteRowsProvenance' sameLocalCert
    provenanceLocalCertEndpoint' endpointAppend' endpointPkg'
  obtain ⟨sourceUnary, reindexUnary, windowsUnary, radiusUnary, sealUnary, sameRowsUnary,
    routeRowsUnary, provenanceUnary, localCertUnary, _endpointUnary, sourceReindexWindows,
    windowsRadiusSeal, sameRowsRouteRowsProvenance, _provenanceLocalCertEndpoint,
    _endpointAppend, _endpointPkg⟩ := carrier
  have sameWindows : hsame windows windows' :=
    cont_respects_hsame sameSource sameReindex sourceReindexWindows sourceReindexWindows'
  have sameSeal : hsame «seal» seal' :=
    cont_respects_hsame sameWindows sameRadius windowsRadiusSeal windowsRadiusSeal'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameSameRows sameRouteRows sameRowsRouteRowsProvenance
      sameRowsRouteRowsProvenance'
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have reindexUnary' : UnaryHistory reindex' := unary_transport reindexUnary sameReindex
  have windowsUnary' : UnaryHistory windows' := unary_transport windowsUnary sameWindows
  have radiusUnary' : UnaryHistory radius' := unary_transport radiusUnary sameRadius
  have sealUnary' : UnaryHistory seal' := unary_transport sealUnary sameSeal
  have sameRowsUnary' : UnaryHistory sameRows' :=
    unary_transport sameRowsUnary sameSameRows
  have routeRowsUnary' : UnaryHistory routeRows' :=
    unary_transport routeRowsUnary sameRouteRows
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' localCertUnary' provenanceLocalCertEndpoint'
  exact
    ⟨⟨sourceUnary', reindexUnary', windowsUnary', radiusUnary', sealUnary', sameRowsUnary',
      routeRowsUnary', provenanceUnary', localCertUnary', endpointUnary', sourceReindexWindows',
      windowsRadiusSeal', sameRowsRouteRowsProvenance', provenanceLocalCertEndpoint',
      endpointAppend', endpointPkg'⟩,
      sameWindows, sameSeal, sameProvenance⟩

theorem RegularCauchySubsequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source reindex windows radius «seal» sameRows routeRows provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubsequenceCarrier source reindex windows radius «seal» sameRows routeRows
        provenance localCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchySubsequenceCarrier source reindex windows radius «seal» sameRows routeRows
            provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          RegularCauchySubsequenceCarrier source reindex windows radius «seal» sameRows routeRows
            provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          RegularCauchySubsequenceCarrier source reindex windows radius «seal» sameRows routeRows
            provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem RegularCauchySubsequenceCarrier_tail_classifier_stability [AskSetup] [PackageSetup]
    {source reindex windows radius «seal» sameRows routeRows provenance localCert endpoint source'
      reindex' windows' radius' seal' sameRows' routeRows' provenance' localCert'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubsequenceCarrier source reindex windows radius «seal» sameRows routeRows
        provenance localCert endpoint bundle pkg ->
      hsame source source' ->
        hsame reindex reindex' ->
          hsame windows windows' ->
            hsame radius radius' ->
              hsame «seal» seal' ->
                hsame sameRows sameRows' ->
                  hsame routeRows routeRows' ->
                    hsame provenance provenance' ->
                      hsame localCert localCert' ->
                        hsame endpoint endpoint' ->
                          PkgSig bundle endpoint' pkg ->
                            RegularCauchySubsequenceCarrier source' reindex' windows' radius'
                              seal' sameRows' routeRows' provenance' localCert' endpoint' bundle
                                pkg := by
  intro carrier sameSource sameReindex sameWindows sameRadius sameSeal sameRowsRoute
    sameRouteRows sameProvenance sameLocalCert sameEndpoint endpointPkg
  obtain ⟨sourceUnary, reindexUnary, windowsUnary, radiusUnary, sealUnary, sameRowsUnary,
    routeRowsUnary, provenanceUnary, localCertUnary, endpointUnary, sourceReindexWindows,
    windowsRadiusSeal, sameRowsRouteRowsProvenance, provenanceLocalCertEndpoint,
    endpointAppend, _endpointPkg⟩ := carrier
  exact
    ⟨unary_transport sourceUnary sameSource,
      unary_transport reindexUnary sameReindex,
      unary_transport windowsUnary sameWindows,
      unary_transport radiusUnary sameRadius,
      unary_transport sealUnary sameSeal,
      unary_transport sameRowsUnary sameRowsRoute,
      unary_transport routeRowsUnary sameRouteRows,
      unary_transport provenanceUnary sameProvenance,
      unary_transport localCertUnary sameLocalCert,
      unary_transport endpointUnary sameEndpoint,
      cont_hsame_transport sameSource sameReindex sameWindows sourceReindexWindows,
      cont_hsame_transport sameWindows sameRadius sameSeal windowsRadiusSeal,
      cont_hsame_transport sameRowsRoute sameRouteRows sameProvenance
        sameRowsRouteRowsProvenance,
      cont_hsame_transport sameProvenance sameLocalCert sameEndpoint provenanceLocalCertEndpoint,
      hsame_trans (hsame_symm sameEndpoint)
        (hsame_trans endpointAppend (by
          cases sameProvenance
          cases sameLocalCert
          exact hsame_refl (append provenance localCert))),
      endpointPkg⟩

theorem RegularCauchySubsequenceCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {source reindex windows radius «seal» sameRows routeRows provenance localCert endpoint
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubsequenceCarrier source reindex windows radius «seal» sameRows routeRows
        provenance localCert endpoint bundle pkg ->
      Cont «seal» localCert consumerRead ->
        UnaryHistory source ∧ UnaryHistory reindex ∧ UnaryHistory windows ∧
          UnaryHistory radius ∧ UnaryHistory «seal» ∧ UnaryHistory consumerRead ∧
            Cont source reindex windows ∧ Cont windows radius «seal» ∧
              Cont provenance localCert endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier sealLocalCertConsumer
  obtain ⟨sourceUnary, reindexUnary, windowsUnary, radiusUnary, sealUnary, _sameRowsUnary,
    _routeRowsUnary, _provenanceUnary, localCertUnary, _endpointUnary, sourceReindexWindows,
    windowsRadiusSeal, _sameRowsRouteRowsProvenance, provenanceLocalCertEndpoint,
    _endpointAppend, endpointPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary localCertUnary sealLocalCertConsumer
  exact
    ⟨sourceUnary, reindexUnary, windowsUnary, radiusUnary, sealUnary, consumerUnary,
      sourceReindexWindows, windowsRadiusSeal, provenanceLocalCertEndpoint, endpointPkg⟩

end BEDC.Derived.RegularCauchySubsequenceUp
