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

end BEDC.Derived.RegularCauchySubsequenceUp
