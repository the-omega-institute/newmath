import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLimitTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLimitTransportCarrier [AskSetup] [PackageSetup]
    (sourceRow windowRow dyadicRow sealRow transportRow routeRow provenanceRow localCertRow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  UnaryHistory sourceRow ∧ UnaryHistory windowRow ∧ UnaryHistory dyadicRow ∧
    UnaryHistory sealRow ∧ UnaryHistory transportRow ∧ UnaryHistory routeRow ∧
      UnaryHistory provenanceRow ∧ UnaryHistory localCertRow ∧
        Cont sourceRow windowRow dyadicRow ∧ Cont dyadicRow sealRow routeRow ∧
          Cont routeRow transportRow provenanceRow ∧ PkgSig bundle provenanceRow pkg ∧
            PkgSig bundle localCertRow pkg

theorem RegularCauchyLimitTransportCarrier_stability [AskSetup] [PackageSetup]
    {sourceRow windowRow dyadicRow sealRow transportRow routeRow provenanceRow localCertRow
      sourceRow' windowRow' dyadicRow' sealRow' routeRow' provenanceRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier sourceRow windowRow dyadicRow sealRow transportRow
        routeRow provenanceRow localCertRow bundle pkg ->
      hsame sourceRow sourceRow' ->
        hsame windowRow windowRow' ->
          hsame sealRow sealRow' ->
            Cont sourceRow' windowRow' dyadicRow' ->
              Cont dyadicRow' sealRow' routeRow' ->
                Cont routeRow' transportRow provenanceRow' ->
                  PkgSig bundle provenanceRow' pkg ->
                    RegularCauchyLimitTransportCarrier sourceRow' windowRow' dyadicRow'
                      sealRow' transportRow routeRow' provenanceRow' localCertRow bundle pkg ∧
                    hsame dyadicRow dyadicRow' ∧ hsame routeRow routeRow' ∧
                      hsame provenanceRow provenanceRow' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier sameSource sameWindow sameSeal sourceWindowDyadic' dyadicSealRoute'
    routeTransportProvenance' provenancePkg'
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, transportUnary, routeUnary,
    provenanceUnary, localCertUnary, sourceWindowDyadic, dyadicSealRoute,
    routeTransportProvenance, _provenancePkg, localCertPkg⟩ := carrier
  have sameDyadic : hsame dyadicRow dyadicRow' :=
    cont_respects_hsame sameSource sameWindow sourceWindowDyadic sourceWindowDyadic'
  have sameRoute : hsame routeRow routeRow' :=
    cont_respects_hsame sameDyadic sameSeal dyadicSealRoute dyadicSealRoute'
  have sameProvenance : hsame provenanceRow provenanceRow' :=
    cont_respects_hsame sameRoute (hsame_refl transportRow) routeTransportProvenance
      routeTransportProvenance'
  have transported :
      RegularCauchyLimitTransportCarrier sourceRow' windowRow' dyadicRow' sealRow'
        transportRow routeRow' provenanceRow' localCertRow bundle pkg := by
    exact
      ⟨unary_transport sourceUnary sameSource, unary_transport windowUnary sameWindow,
        unary_transport dyadicUnary sameDyadic, unary_transport sealUnary sameSeal,
        transportUnary, unary_transport routeUnary sameRoute,
        unary_transport provenanceUnary sameProvenance, localCertUnary, sourceWindowDyadic',
        dyadicSealRoute', routeTransportProvenance', provenancePkg', localCertPkg⟩
  exact ⟨transported, sameDyadic, sameRoute, sameProvenance⟩

end BEDC.Derived.RegularCauchyLimitTransportUp
