import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.StoneDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem StoneDualityClopenLedger_transport_closure [AskSetup] [PackageSetup]
    {booleanRow booleanRow' clopenRow clopenRow' ledger ledger' provenance endpoint
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame booleanRow booleanRow' -> hsame clopenRow clopenRow' ->
      Cont booleanRow clopenRow ledger -> Cont booleanRow' clopenRow' ledger' ->
        Cont ledger provenance endpoint -> Cont ledger' provenance endpoint' ->
          PkgSig bundle endpoint pkg -> hsame endpoint endpoint' := by
  intro sameBoolean sameClopen ledgerRow ledgerRow' endpointRow endpointRow' _pkgSig
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameBoolean sameClopen ledgerRow ledgerRow'
  exact cont_respects_hsame sameLedger (hsame_refl provenance) endpointRow endpointRow'

end BEDC.Derived.StoneDualityUp
