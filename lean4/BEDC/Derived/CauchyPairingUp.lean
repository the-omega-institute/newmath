import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

end BEDC.Derived.CauchyPairingUp
