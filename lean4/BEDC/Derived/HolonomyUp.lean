import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HolonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HolonomyBHistTransportCarrier [AskSetup] [PackageSetup]
    (bundleRow connectionRow loopRow endpointRow curvatureRow controlRow ledgerRow
      dependencyRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundleRow ∧ UnaryHistory connectionRow ∧ UnaryHistory endpointRow ∧
    UnaryHistory curvatureRow ∧ UnaryHistory controlRow ∧ UnaryHistory loopRow ∧
      UnaryHistory ledgerRow ∧ UnaryHistory dependencyRow ∧
        Cont bundleRow connectionRow loopRow ∧ Cont loopRow endpointRow ledgerRow ∧
          Cont curvatureRow controlRow dependencyRow ∧ PkgSig bundle dependencyRow pkg

theorem HolonomyBHistTransportCarrier_continuation_transport_stability [AskSetup]
    [PackageSetup]
    {bundleRow connectionRow loopRow endpointRow curvatureRow controlRow ledgerRow
      dependencyRow bundleRow' connectionRow' loopRow' endpointRow' curvatureRow'
      controlRow' ledgerRow' dependencyRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyBHistTransportCarrier bundleRow connectionRow loopRow endpointRow curvatureRow
        controlRow ledgerRow dependencyRow bundle pkg ->
      hsame bundleRow bundleRow' ->
        hsame connectionRow connectionRow' ->
          hsame endpointRow endpointRow' ->
            hsame curvatureRow curvatureRow' ->
              hsame controlRow controlRow' ->
                Cont bundleRow' connectionRow' loopRow' ->
                  Cont loopRow' endpointRow' ledgerRow' ->
                    Cont curvatureRow' controlRow' dependencyRow' ->
                      PkgSig bundle dependencyRow' pkg ->
                        HolonomyBHistTransportCarrier bundleRow' connectionRow' loopRow'
                            endpointRow' curvatureRow' controlRow' ledgerRow' dependencyRow'
                            bundle pkg ∧
                          hsame loopRow loopRow' ∧ hsame ledgerRow ledgerRow' ∧
                            hsame dependencyRow dependencyRow' := by
  intro carrier sameBundle sameConnection sameEndpoint sameCurvature sameControl
    loopRow'Cont ledgerRow'Cont dependencyRow'Cont pkg'
  have bundleUnary' : UnaryHistory bundleRow' :=
    unary_transport carrier.left sameBundle
  have connectionUnary' : UnaryHistory connectionRow' :=
    unary_transport carrier.right.left sameConnection
  have endpointUnary' : UnaryHistory endpointRow' :=
    unary_transport carrier.right.right.left sameEndpoint
  have curvatureUnary' : UnaryHistory curvatureRow' :=
    unary_transport carrier.right.right.right.left sameCurvature
  have controlUnary' : UnaryHistory controlRow' :=
    unary_transport carrier.right.right.right.right.left sameControl
  have sameLoop : hsame loopRow loopRow' :=
    cont_respects_hsame sameBundle sameConnection
      carrier.right.right.right.right.right.right.right.right.left loopRow'Cont
  have loopUnary' : UnaryHistory loopRow' :=
    unary_cont_closed bundleUnary' connectionUnary' loopRow'Cont
  have sameLedger : hsame ledgerRow ledgerRow' :=
    cont_respects_hsame sameLoop sameEndpoint
      carrier.right.right.right.right.right.right.right.right.right.left ledgerRow'Cont
  have ledgerUnary' : UnaryHistory ledgerRow' :=
    unary_cont_closed loopUnary' endpointUnary' ledgerRow'Cont
  have sameDependency : hsame dependencyRow dependencyRow' :=
    cont_respects_hsame sameCurvature sameControl
      carrier.right.right.right.right.right.right.right.right.right.right.left
      dependencyRow'Cont
  have dependencyUnary' : UnaryHistory dependencyRow' :=
    unary_cont_closed curvatureUnary' controlUnary' dependencyRow'Cont
  exact
    And.intro
      (And.intro bundleUnary'
        (And.intro connectionUnary'
          (And.intro endpointUnary'
            (And.intro curvatureUnary'
              (And.intro controlUnary'
                (And.intro loopUnary'
                  (And.intro ledgerUnary'
                    (And.intro dependencyUnary'
                      (And.intro loopRow'Cont
                        (And.intro ledgerRow'Cont
                          (And.intro dependencyRow'Cont pkg')))))))))))
      (And.intro sameLoop (And.intro sameLedger sameDependency))

end BEDC.Derived.HolonomyUp
