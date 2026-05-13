import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

/-!
# CauchyPairingUp finite carrier surface.
-/

namespace BEDC.Derived.CauchyPairingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def CauchyPairingCarrier [AskSetup] [PackageSetup]
    (a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory wA ∧ UnaryHistory wB ∧
    UnaryHistory lA ∧ UnaryHistory lB ∧ UnaryHistory muA ∧ UnaryHistory muB ∧
      UnaryHistory mu ∧ UnaryHistory eA ∧ UnaryHistory eB ∧ UnaryHistory e ∧
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
          UnaryHistory localCert ∧
            Cont mu wA lA ∧ Cont mu wB lB ∧ Cont lA lB e ∧
              Cont e provenance transport ∧ Cont transport localCert route ∧
                PkgSig bundle e pkg

theorem CauchyPairingCarrier_classifier_transport_exactness [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert
      a' b' wA' wB' lA' lB' muA' muB' mu' eA' eB' e' transport' route'
      provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      hsame a a' ->
        hsame b b' ->
          hsame wA wA' ->
            hsame wB wB' ->
              hsame muA muA' ->
                hsame muB muB' ->
                  hsame mu mu' ->
                    hsame eA eA' ->
                      hsame eB eB' ->
                        hsame provenance provenance' ->
                          hsame localCert localCert' ->
                            Cont mu' wA' lA' ->
                              Cont mu' wB' lB' ->
                                Cont lA' lB' e' ->
                                  Cont e' provenance' transport' ->
                                    Cont transport' localCert' route' ->
                                      PkgSig bundle e' pkg ->
                                        CauchyPairingCarrier a' b' wA' wB' lA' lB'
                                            muA' muB' mu' eA' eB' e' transport'
                                            route' provenance' localCert' bundle pkg ∧
                                          hsame lA lA' ∧ hsame lB lB' ∧ hsame e e' := by
  intro carrier sameA sameB sameWA sameWB sameMuA sameMuB sameMu sameEA sameEB
    sameProvenance sameLocalCert lARow' lBRow' eRow' transportRow' routeRow' pkgSig'
  rcases carrier with
    ⟨aUnary, bUnary, wAUnary, wBUnary, _lAUnary, _lBUnary, muAUnary, muBUnary,
      muUnary, eAUnary, eBUnary, _eUnary, _transportUnary, _routeUnary, provenanceUnary,
      localCertUnary, lARow, lBRow, eRow, _transportRow, _routeRow, _pkgSig⟩
  have aUnary' : UnaryHistory a' :=
    unary_transport aUnary sameA
  have bUnary' : UnaryHistory b' :=
    unary_transport bUnary sameB
  have wAUnary' : UnaryHistory wA' :=
    unary_transport wAUnary sameWA
  have wBUnary' : UnaryHistory wB' :=
    unary_transport wBUnary sameWB
  have muAUnary' : UnaryHistory muA' :=
    unary_transport muAUnary sameMuA
  have muBUnary' : UnaryHistory muB' :=
    unary_transport muBUnary sameMuB
  have muUnary' : UnaryHistory mu' :=
    unary_transport muUnary sameMu
  have eAUnary' : UnaryHistory eA' :=
    unary_transport eAUnary sameEA
  have eBUnary' : UnaryHistory eB' :=
    unary_transport eBUnary sameEB
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have lAUnary' : UnaryHistory lA' :=
    unary_cont_closed muUnary' wAUnary' lARow'
  have lBUnary' : UnaryHistory lB' :=
    unary_cont_closed muUnary' wBUnary' lBRow'
  have eUnary' : UnaryHistory e' :=
    unary_cont_closed lAUnary' lBUnary' eRow'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed eUnary' provenanceUnary' transportRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed transportUnary' localCertUnary' routeRow'
  have sameLA : hsame lA lA' :=
    cont_respects_hsame sameMu sameWA lARow lARow'
  have sameLB : hsame lB lB' :=
    cont_respects_hsame sameMu sameWB lBRow lBRow'
  have sameE : hsame e e' :=
    cont_respects_hsame sameLA sameLB eRow eRow'
  have targetCarrier :
      CauchyPairingCarrier a' b' wA' wB' lA' lB' muA' muB' mu' eA' eB' e'
        transport' route' provenance' localCert' bundle pkg :=
    ⟨aUnary', bUnary', wAUnary', wBUnary', lAUnary', lBUnary', muAUnary', muBUnary',
      muUnary', eAUnary', eBUnary', eUnary', transportUnary', routeUnary',
      provenanceUnary', localCertUnary', lARow', lBRow', eRow', transportRow', routeRow',
      pkgSig'⟩
  exact And.intro targetCarrier
    (And.intro sameLA (And.intro sameLB sameE))

theorem CauchyPairingCarrier_paired_seal_non_escape [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert
      sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      Cont e provenance sealConsumer ->
        PkgSig bundle sealConsumer pkg ->
          UnaryHistory wA ∧ UnaryHistory wB ∧ UnaryHistory lA ∧ UnaryHistory lB ∧
            UnaryHistory e ∧ UnaryHistory sealConsumer ∧ Cont mu wA lA ∧
              Cont mu wB lB ∧ Cont lA lB e ∧ Cont e provenance sealConsumer ∧
                PkgSig bundle e pkg ∧ PkgSig bundle sealConsumer pkg := by
  intro carrier eProvenanceSealConsumer sealConsumerPkg
  obtain ⟨_aUnary, _bUnary, wAUnary, wBUnary, lAUnary, lBUnary, _muAUnary,
    _muBUnary, _muUnary, _eAUnary, _eBUnary, eUnary, _transportUnary, _routeUnary,
    provenanceUnary, _localCertUnary, muWARow, muWBRow, lAlBRow, _eProvenanceTransport,
    _transportLocalRoute, ePkg⟩ := carrier
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed eUnary provenanceUnary eProvenanceSealConsumer
  exact
    ⟨wAUnary, wBUnary, lAUnary, lBUnary, eUnary, sealConsumerUnary, muWARow,
      muWBRow, lAlBRow, eProvenanceSealConsumer, ePkg, sealConsumerPkg⟩

theorem CauchyPairingCarrier_shared_bound_consumer [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert
      sharedBound : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      Cont muA muB sharedBound ->
        PkgSig bundle sharedBound pkg ->
          UnaryHistory mu ∧ UnaryHistory muA ∧ UnaryHistory muB ∧
            UnaryHistory sharedBound ∧ Cont mu wA lA ∧ Cont mu wB lB ∧
              Cont muA muB sharedBound ∧ PkgSig bundle e pkg ∧
                PkgSig bundle sharedBound pkg := by
  intro carrier sharedBoundRow sharedBoundPkg
  obtain ⟨_aUnary, _bUnary, _wAUnary, _wBUnary, _lAUnary, _lBUnary, muAUnary,
    muBUnary, muUnary, _eAUnary, _eBUnary, _eUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, muWARow, muWBRow, _lAlBRow,
    _eProvenanceTransport, _transportLocalRoute, ePkg⟩ := carrier
  have sharedBoundUnary : UnaryHistory sharedBound :=
    unary_cont_closed muAUnary muBUnary sharedBoundRow
  exact
    ⟨muUnary, muAUnary, muBUnary, sharedBoundUnary, muWARow, muWBRow, sharedBoundRow,
      ePkg, sharedBoundPkg⟩

theorem CauchyPairingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
            provenance localCert bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
            provenance localCert bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
            provenance localCert bundle pkg ∧ hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro carrier (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchyPairingCarrier_public_rows_zero_head_absurd [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert
      zWA zWB zE : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      (hsame wA (BHist.e0 zWA) -> False) ∧
        (hsame wB (BHist.e0 zWB) -> False) ∧
          (hsame e (BHist.e0 zE) -> False) := by
  intro carrier
  obtain ⟨_aUnary, _bUnary, wAUnary, wBUnary, _lAUnary, _lBUnary, _muAUnary,
    _muBUnary, _muUnary, _eAUnary, _eBUnary, eUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, _muWARow, _muWBRow, _lAlBRow,
    _eProvenanceTransport, _transportLocalRoute, _ePkg⟩ := carrier
  constructor
  · intro sameWAZero
    exact unary_no_zero_extension (unary_transport wAUnary sameWAZero)
  constructor
  · intro sameWBZero
    exact unary_no_zero_extension (unary_transport wBUnary sameWBZero)
  · intro sameEZero
    exact unary_no_zero_extension (unary_transport eUnary sameEZero)

theorem CauchyPairingCarrier_synchronized_window_stability [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert
      mu' wA' wB' lA' lB' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      hsame mu mu' ->
        hsame wA wA' ->
          hsame wB wB' ->
            Cont mu' wA' lA' ->
              Cont mu' wB' lB' ->
                UnaryHistory lA' ∧ UnaryHistory lB' ∧ hsame lA lA' ∧ hsame lB lB' := by
  intro carrier sameMu sameWA sameWB lARow' lBRow'
  obtain ⟨_aUnary, _bUnary, wAUnary, wBUnary, _lAUnary, _lBUnary, _muAUnary,
    _muBUnary, muUnary, _eAUnary, _eBUnary, _eUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, lARow, lBRow, _lAlBRow, _eProvenanceTransport,
    _transportLocalRoute, _pkgSig⟩ := carrier
  have muUnary' : UnaryHistory mu' :=
    unary_transport muUnary sameMu
  have wAUnary' : UnaryHistory wA' :=
    unary_transport wAUnary sameWA
  have wBUnary' : UnaryHistory wB' :=
    unary_transport wBUnary sameWB
  have lAUnary' : UnaryHistory lA' :=
    unary_cont_closed muUnary' wAUnary' lARow'
  have lBUnary' : UnaryHistory lB' :=
    unary_cont_closed muUnary' wBUnary' lBRow'
  have sameLA : hsame lA lA' :=
    cont_respects_hsame sameMu sameWA lARow lARow'
  have sameLB : hsame lB lB' :=
    cont_respects_hsame sameMu sameWB lBRow lBRow'
  exact And.intro lAUnary'
    (And.intro lBUnary' (And.intro sameLA sameLB))

theorem CauchyPairingCarrier_scoped_dependency_package [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert
      exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      Cont route provenance exportRow ->
        PkgSig bundle exportRow pkg ->
          UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory wA ∧ UnaryHistory wB ∧
            UnaryHistory lA ∧ UnaryHistory lB ∧ UnaryHistory e ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory exportRow ∧ Cont mu wA lA ∧
                Cont mu wB lB ∧ Cont lA lB e ∧ Cont route provenance exportRow ∧
                  PkgSig bundle e pkg ∧ PkgSig bundle exportRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier routeProvenanceExport exportPkg
  obtain ⟨aUnary, bUnary, wAUnary, wBUnary, lAUnary, lBUnary, _muAUnary, _muBUnary,
    _muUnary, _eAUnary, _eBUnary, eUnary, _transportUnary, routeUnary, provenanceUnary,
    _localCertUnary, muWARow, muWBRow, lAlBRow, _eProvenanceTransport,
    _transportLocalRoute, ePkg⟩ := carrier
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceExport
  exact
    ⟨aUnary, bUnary, wAUnary, wBUnary, lAUnary, lBUnary, eUnary, routeUnary,
      provenanceUnary, exportUnary, muWARow, muWBRow, lAlBRow, routeProvenanceExport,
      ePkg, exportPkg⟩

theorem CauchyPairingCarrier_meet_source [AskSetup] [PackageSetup]
    {a b wA wB lA lB muA muB mu eA eB e transport route provenance localCert
      meetRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyPairingCarrier a b wA wB lA lB muA muB mu eA eB e transport route
        provenance localCert bundle pkg ->
      Cont muA muB meetRow ->
        UnaryHistory muA ∧ UnaryHistory muB ∧ UnaryHistory mu ∧ UnaryHistory meetRow ∧
          Cont muA muB meetRow ∧ Cont mu wA lA ∧ Cont mu wB lB ∧
            UnaryHistory lA ∧ UnaryHistory lB ∧ PkgSig bundle e pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier meetCont
  obtain ⟨_aUnary, _bUnary, wAUnary, wBUnary, lAUnary, lBUnary, muAUnary,
    muBUnary, muUnary, _eAUnary, _eBUnary, _eUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, muWARow, muWBRow, _lAlBRow, _eProvenanceTransport,
    _transportLocalRoute, ePkg⟩ := carrier
  have meetUnary : UnaryHistory meetRow :=
    unary_cont_closed muAUnary muBUnary meetCont
  exact
    ⟨muAUnary, muBUnary, muUnary, meetUnary, meetCont, muWARow, muWBRow, lAUnary,
      lBUnary, ePkg⟩

end BEDC.Derived.CauchyPairingUp
