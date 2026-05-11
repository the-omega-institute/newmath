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
    (object cofibrant arrow factorization lifting packageRow ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory factorization ∧
    UnaryHistory packageRow ∧ UnaryHistory ledger ∧ Cont object cofibrant arrow ∧
      Cont arrow factorization lifting ∧ Cont packageRow lifting endpoint ∧
        PkgSig bundle endpoint pkg

theorem CofibrantReplacementBHistSource_factorization_transport [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting packageRow ledger endpoint object' cofibrant'
      arrow' factorization' lifting' packageRow' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting packageRow ledger
        endpoint bundle pkg ->
      hsame object object' ->
        hsame cofibrant cofibrant' ->
          hsame factorization factorization' ->
            hsame packageRow packageRow' ->
              hsame ledger ledger' ->
              Cont object' cofibrant' arrow' ->
                Cont arrow' factorization' lifting' ->
                  Cont packageRow' lifting' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      CofibrantReplacementBHistSource object' cofibrant' arrow' factorization'
                          lifting' packageRow' ledger' endpoint' bundle pkg ∧
                        hsame arrow arrow' ∧ hsame lifting lifting' ∧ hsame endpoint endpoint' := by
  intro source sameObject sameCofibrant sameFactorization samePackageRow sameLedger
  intro targetObject targetFactorization targetEndpoint targetEndpointSig
  have objectUnary' : UnaryHistory object' :=
    unary_transport source.left sameObject
  have cofibrantUnary' : UnaryHistory cofibrant' :=
    unary_transport source.right.left sameCofibrant
  have factorizationUnary' : UnaryHistory factorization' :=
    unary_transport source.right.right.left sameFactorization
  have packageRowUnary' : UnaryHistory packageRow' :=
    unary_transport source.right.right.right.left samePackageRow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport source.right.right.right.right.left sameLedger
  have sameArrow : hsame arrow arrow' :=
    cont_respects_hsame sameObject sameCofibrant source.right.right.right.right.right.left
      targetObject
  have sameLifting : hsame lifting lifting' :=
    cont_respects_hsame sameArrow sameFactorization source.right.right.right.right.right.right.left
      targetFactorization
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePackageRow sameLifting
      source.right.right.right.right.right.right.right.left targetEndpoint
  exact
    And.intro
      (And.intro objectUnary'
        (And.intro cofibrantUnary'
          (And.intro factorizationUnary'
            (And.intro packageRowUnary'
              (And.intro ledgerUnary'
                (And.intro targetObject
                  (And.intro targetFactorization
                    (And.intro targetEndpoint targetEndpointSig))))))))
      (And.intro sameArrow (And.intro sameLifting sameEndpoint))

theorem CofibrantReplacementBHistSource_factorization_obligation [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting packageRow ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting packageRow
        ledger endpoint bundle pkg ->
      UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory arrow ∧
        UnaryHistory factorization ∧ UnaryHistory lifting ∧ UnaryHistory packageRow ∧
          UnaryHistory endpoint ∧ Cont object cofibrant arrow ∧
            Cont arrow factorization lifting ∧ Cont packageRow lifting endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro source
  have objectUnary : UnaryHistory object :=
    source.left
  have cofibrantUnary : UnaryHistory cofibrant :=
    source.right.left
  have factorizationUnary : UnaryHistory factorization :=
    source.right.right.left
  have packageRowUnary : UnaryHistory packageRow :=
    source.right.right.right.left
  have objectCofibrantArrow : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have arrowFactorizationLifting : Cont arrow factorization lifting :=
    source.right.right.right.right.right.right.left
  have packageLiftingEndpoint : Cont packageRow lifting endpoint :=
    source.right.right.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    source.right.right.right.right.right.right.right.right
  have arrowUnary : UnaryHistory arrow :=
    unary_cont_closed objectUnary cofibrantUnary objectCofibrantArrow
  have liftingUnary : UnaryHistory lifting :=
    unary_cont_closed arrowUnary factorizationUnary arrowFactorizationLifting
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed packageRowUnary liftingUnary packageLiftingEndpoint
  exact And.intro objectUnary
    (And.intro cofibrantUnary
      (And.intro arrowUnary
        (And.intro factorizationUnary
          (And.intro liftingUnary
            (And.intro packageRowUnary
              (And.intro endpointUnary
                (And.intro objectCofibrantArrow
                  (And.intro arrowFactorizationLifting
                    (And.intro packageLiftingEndpoint endpointPkg)))))))))

end BEDC.Derived.CofibrantReplacementUp
