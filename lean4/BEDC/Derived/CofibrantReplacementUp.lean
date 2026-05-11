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
    (object cofibrant arrow factorization lifting dependency ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory factorization ∧
    UnaryHistory lifting ∧ UnaryHistory dependency ∧ Cont object cofibrant arrow ∧
      Cont arrow factorization ledger ∧ Cont ledger dependency endpoint ∧
        PkgSig bundle endpoint pkg

theorem CofibrantReplacementBHistSource_factorization_transport [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting pkgrow ledger object' cofibrant' arrow'
      factorization' lifting' pkgrow' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting pkgrow ledger
        (append ledger pkgrow) bundle pkg ->
      hsame object object' ->
        hsame cofibrant cofibrant' ->
          hsame factorization factorization' ->
            hsame pkgrow pkgrow' ->
              UnaryHistory lifting' ->
                Cont object' cofibrant' arrow' ->
                  Cont arrow' factorization' ledger' ->
                    Cont ledger' pkgrow' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        CofibrantReplacementBHistSource object' cofibrant' arrow' factorization'
                            lifting' pkgrow' ledger' endpoint' bundle pkg ∧
                          hsame arrow arrow' ∧ hsame ledger ledger' ∧
                            hsame (append ledger pkgrow) endpoint' := by
  intro source sameObject sameCofibrant sameFactorization samePkgrow
  intro liftingUnary' targetObject targetFactorization targetPkg targetPkgSig
  have objectUnary' : UnaryHistory object' :=
    unary_transport source.left sameObject
  have cofibrantUnary' : UnaryHistory cofibrant' :=
    unary_transport source.right.left sameCofibrant
  have factorizationUnary' : UnaryHistory factorization' :=
    unary_transport source.right.right.left sameFactorization
  have pkgrowUnary' : UnaryHistory pkgrow' :=
    unary_transport source.right.right.right.right.left samePkgrow
  have sameArrow : hsame arrow arrow' :=
    cont_respects_hsame sameObject sameCofibrant
      source.right.right.right.right.right.left targetObject
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameArrow sameFactorization
      source.right.right.right.right.right.right.left targetFactorization
  have sameEndpoint : hsame (append ledger pkgrow) endpoint' :=
    cont_respects_hsame sameLedger samePkgrow
      source.right.right.right.right.right.right.right.left targetPkg
  exact
    And.intro
      (And.intro objectUnary'
        (And.intro cofibrantUnary'
          (And.intro factorizationUnary'
            (And.intro liftingUnary'
              (And.intro pkgrowUnary'
                (And.intro targetObject
                  (And.intro targetFactorization (And.intro targetPkg targetPkgSig))))))))
      (And.intro sameArrow (And.intro sameLedger sameEndpoint))

theorem CofibrantReplacementBHistSource_factorization_obligation [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory arrow ∧
        UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory dependency ∧
          UnaryHistory endpoint ∧ Cont object cofibrant arrow ∧
            Cont arrow factorization ledger ∧ Cont ledger dependency endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro source
  have objectUnary : UnaryHistory object :=
    source.left
  have cofibrantUnary : UnaryHistory cofibrant :=
    source.right.left
  have factorizationUnary : UnaryHistory factorization :=
    source.right.right.left
  have liftingUnary : UnaryHistory lifting :=
    source.right.right.right.left
  have dependencyUnary : UnaryHistory dependency :=
    source.right.right.right.right.left
  have arrowRow : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have ledgerRow : Cont arrow factorization ledger :=
    source.right.right.right.right.right.right.left
  have endpointRow : Cont ledger dependency endpoint :=
    source.right.right.right.right.right.right.right.left
  have packageBoundary : PkgSig bundle endpoint pkg :=
    source.right.right.right.right.right.right.right.right
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary arrowRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary dependencyUnary endpointRow
  exact And.intro objectUnary
    (And.intro cofibrantUnary
      (And.intro arrowUnary
        (And.intro factorizationUnary
          (And.intro liftingUnary
            (And.intro dependencyUnary
              (And.intro endpointUnary
                (And.intro arrowRow
                  (And.intro ledgerRow (And.intro endpointRow packageBoundary)))))))))

theorem CofibrantReplacementBHistSource_factorization_readback [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting dependency ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting dependency
        ledger endpoint bundle pkg ->
      UnaryHistory arrow ∧ UnaryHistory ledger ∧ hsame ledger (append arrow factorization) ∧
        UnaryHistory endpoint ∧ hsame endpoint (append ledger dependency) ∧
          PkgSig bundle endpoint pkg := by
  intro source
  have objectUnary : UnaryHistory object :=
    source.left
  have cofibrantUnary : UnaryHistory cofibrant :=
    source.right.left
  have factorizationUnary : UnaryHistory factorization :=
    source.right.right.left
  have dependencyUnary : UnaryHistory dependency :=
    source.right.right.right.right.left
  have arrowRow : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have ledgerRow : Cont arrow factorization ledger :=
    source.right.right.right.right.right.right.left
  have endpointRow : Cont ledger dependency endpoint :=
    source.right.right.right.right.right.right.right.left
  have packageBoundary : PkgSig bundle endpoint pkg :=
    source.right.right.right.right.right.right.right.right
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary arrowRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed arrowUnary factorizationUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary dependencyUnary endpointRow
  exact And.intro arrowUnary
    (And.intro ledgerUnary
      (And.intro ledgerRow
        (And.intro endpointUnary
          (And.intro endpointRow packageBoundary))))

end BEDC.Derived.CofibrantReplacementUp
