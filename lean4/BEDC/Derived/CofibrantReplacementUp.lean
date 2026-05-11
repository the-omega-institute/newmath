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
    (object cofibrant arrow factorization liftingTests deps contLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory object ∧ UnaryHistory cofibrant ∧ UnaryHistory arrow ∧
    UnaryHistory factorization ∧ UnaryHistory deps ∧
      Cont object cofibrant arrow ∧
        Cont arrow factorization liftingTests ∧
          Cont liftingTests deps contLedger ∧
            Cont contLedger factorization endpoint ∧ PkgSig bundle endpoint pkg

theorem CofibrantReplacementBHistSource_factorization_transport [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization liftingTests deps contLedger endpoint object'
      cofibrant' arrow' factorization' liftingTests' deps' contLedger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization liftingTests deps
        contLedger endpoint bundle pkg ->
      hsame object object' ->
        hsame cofibrant cofibrant' ->
          hsame factorization factorization' ->
            hsame deps deps' ->
              UnaryHistory object' ->
                UnaryHistory cofibrant' ->
                  UnaryHistory arrow' ->
                    Cont object' cofibrant' arrow' ->
                      Cont arrow' factorization' liftingTests' ->
                        Cont liftingTests' deps' contLedger' ->
                          Cont contLedger' factorization' endpoint' ->
                            PkgSig bundle endpoint' pkg ->
                              CofibrantReplacementBHistSource object' cofibrant' arrow'
                                  factorization' liftingTests' deps' contLedger' endpoint'
                                  bundle pkg ∧
                                hsame arrow arrow' ∧ hsame liftingTests liftingTests' ∧
                                  hsame contLedger contLedger' ∧ hsame endpoint endpoint' := by
  intro source sameObject sameCofibrant sameFactorization sameDeps
  intro objectUnary' cofibrantUnary' arrowUnary' targetObject targetFactorization
  intro targetDeps targetEndpoint targetPkgSig
  have arrowCont : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have sameArrow : hsame arrow arrow' :=
    cont_respects_hsame sameObject sameCofibrant arrowCont targetObject
  have factorizationUnary' : UnaryHistory factorization' :=
    unary_transport source.right.right.right.left sameFactorization
  have depsUnary' : UnaryHistory deps' :=
    unary_transport source.right.right.right.right.left sameDeps
  have liftingTestsUnary' : UnaryHistory liftingTests' :=
    unary_cont_closed arrowUnary' factorizationUnary' targetFactorization
  have contLedgerUnary' : UnaryHistory contLedger' :=
    unary_cont_closed liftingTestsUnary' depsUnary' targetDeps
  have sameLiftingTests : hsame liftingTests liftingTests' :=
    cont_respects_hsame sameArrow sameFactorization source.right.right.right.right.right.right.left
      targetFactorization
  have sameContLedger : hsame contLedger contLedger' :=
    cont_respects_hsame sameLiftingTests sameDeps source.right.right.right.right.right.right.right.left
      targetDeps
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameContLedger sameFactorization
      source.right.right.right.right.right.right.right.right.left targetEndpoint
  exact
    And.intro
      (And.intro objectUnary'
        (And.intro cofibrantUnary'
          (And.intro arrowUnary'
            (And.intro factorizationUnary'
              (And.intro depsUnary'
                (And.intro targetObject
                  (And.intro targetFactorization
                    (And.intro targetDeps (And.intro targetEndpoint targetPkgSig)))))))))
      (And.intro sameArrow
        (And.intro sameLiftingTests (And.intro sameContLedger sameEndpoint)))

theorem CofibrantReplacementBHistSource_weak_equivalence_ledger [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization liftingTests deps contLedger endpoint factorization'
      liftingTests' contLedger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization liftingTests deps
        contLedger endpoint bundle pkg ->
      hsame factorization factorization' ->
        Cont arrow factorization' liftingTests' ->
          Cont liftingTests' deps contLedger' ->
            Cont contLedger' factorization' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                CofibrantReplacementBHistSource object cofibrant arrow factorization'
                    liftingTests' deps contLedger' endpoint' bundle pkg ∧
                  hsame liftingTests liftingTests' ∧
                    hsame contLedger contLedger' ∧ hsame endpoint endpoint' := by
  intro source sameFactorization liftingTestsCont' contLedgerCont' endpointCont' pkgSig'
  have objectUnary : UnaryHistory object := source.left
  have cofibrantUnary : UnaryHistory cofibrant := source.right.left
  have arrowUnary : UnaryHistory arrow := source.right.right.left
  have factorizationUnary : UnaryHistory factorization := source.right.right.right.left
  have depsUnary : UnaryHistory deps := source.right.right.right.right.left
  have liftingTestsCont : Cont arrow factorization liftingTests :=
    source.right.right.right.right.right.right.left
  have contLedgerCont : Cont liftingTests deps contLedger :=
    source.right.right.right.right.right.right.right.left
  have endpointCont : Cont contLedger factorization endpoint :=
    source.right.right.right.right.right.right.right.right.left
  have objectCont : Cont object cofibrant arrow :=
    source.right.right.right.right.right.left
  have factorizationUnary' : UnaryHistory factorization' :=
    unary_transport factorizationUnary sameFactorization
  have liftingTestsUnary' : UnaryHistory liftingTests' :=
    unary_cont_closed arrowUnary factorizationUnary' liftingTestsCont'
  have contLedgerUnary' : UnaryHistory contLedger' :=
    unary_cont_closed liftingTestsUnary' depsUnary contLedgerCont'
  have sameLiftingTests : hsame liftingTests liftingTests' :=
    cont_respects_hsame (hsame_refl arrow) sameFactorization liftingTestsCont
      liftingTestsCont'
  have sameContLedger : hsame contLedger contLedger' :=
    cont_respects_hsame sameLiftingTests (hsame_refl deps) contLedgerCont contLedgerCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameContLedger sameFactorization endpointCont endpointCont'
  constructor
  · exact And.intro objectUnary
      (And.intro cofibrantUnary
        (And.intro arrowUnary
          (And.intro factorizationUnary'
            (And.intro depsUnary
              (And.intro objectCont
                (And.intro liftingTestsCont'
                  (And.intro contLedgerCont'
                    (And.intro endpointCont' pkgSig'))))))))
  · exact And.intro sameLiftingTests (And.intro sameContLedger sameEndpoint)

end BEDC.Derived.CofibrantReplacementUp
