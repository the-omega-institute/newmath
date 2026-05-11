import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofibrantReplacementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CofibrantReplacementBHistSource [AskSetup] [PackageSetup]
    (object cofibrant arrow factorization lifting pkgrow ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont object cofibrant arrow ∧ Cont arrow factorization lifting ∧
    Cont lifting pkgrow ledger ∧ PkgSig bundle pkgrow pkg

theorem CofibrantReplacementBHistSource_factorization_transport [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting pkgrow ledger object' cofibrant' arrow'
      factorization' lifting' pkgrow' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting pkgrow ledger
        bundle pkg ->
      hsame object object' ->
        hsame cofibrant cofibrant' ->
          hsame factorization factorization' ->
            hsame pkgrow pkgrow' ->
              Cont object' cofibrant' arrow' ->
                Cont arrow' factorization' lifting' ->
                  Cont lifting' pkgrow' ledger' ->
                    PkgSig bundle pkgrow' pkg ->
                      CofibrantReplacementBHistSource object' cofibrant' arrow' factorization'
                          lifting' pkgrow' ledger' bundle pkg ∧
                        hsame arrow arrow' ∧ hsame lifting lifting' ∧ hsame ledger ledger' := by
  intro source sameObject sameCofibrant sameFactorization samePkgrow
  intro targetObject targetFactorization targetPkg targetPkgSig
  have sameArrow : hsame arrow arrow' :=
    cont_respects_hsame sameObject sameCofibrant source.left targetObject
  have sameLifting : hsame lifting lifting' :=
    cont_respects_hsame sameArrow sameFactorization source.right.left targetFactorization
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLifting samePkgrow source.right.right.left targetPkg
  exact
    And.intro
      (And.intro targetObject
        (And.intro targetFactorization (And.intro targetPkg targetPkgSig)))
      (And.intro sameArrow (And.intro sameLifting sameLedger))

def CofibrantReplacementPacket [AskSetup] [PackageSetup]
    (X Q arrow factorization lifting package ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory Q ∧ UnaryHistory arrow ∧ UnaryHistory factorization ∧
    UnaryHistory lifting ∧ UnaryHistory package ∧ Cont arrow factorization ledger ∧
      Cont ledger package endpoint ∧ PkgSig bundle endpoint pkg

theorem CofibrantReplacementPacket_weak_equivalence_ledger_transport [AskSetup]
    [PackageSetup]
    {X Q arrow factorization lifting package ledger endpoint X' Q' arrow' factorization'
      lifting' package' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementPacket X Q arrow factorization lifting package ledger endpoint
        bundle pkg ->
      hsame X X' -> hsame Q Q' -> hsame arrow arrow' ->
        hsame factorization factorization' -> hsame lifting lifting' ->
          hsame package package' -> Cont arrow' factorization' ledger' ->
            Cont ledger' package' endpoint' -> PkgSig bundle endpoint' pkg ->
              CofibrantReplacementPacket X' Q' arrow' factorization' lifting' package'
                  ledger' endpoint' bundle pkg ∧
                hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameX sameQ sameArrow sameFactorization sameLifting samePackage
  intro ledgerRow' endpointRow' pkgSig'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameArrow sameFactorization
      packet.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger samePackage
      packet.right.right.right.right.right.right.right.left endpointRow'
  have transported :
      CofibrantReplacementPacket X' Q' arrow' factorization' lifting' package' ledger'
          endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameX,
      unary_transport packet.right.left sameQ,
      unary_transport packet.right.right.left sameArrow,
      unary_transport packet.right.right.right.left sameFactorization,
      unary_transport packet.right.right.right.right.left sameLifting,
      unary_transport packet.right.right.right.right.right.left samePackage,
      ledgerRow',
      endpointRow',
      pkgSig'⟩
  exact ⟨transported, sameLedger, sameEndpoint⟩

end BEDC.Derived.CofibrantReplacementUp
