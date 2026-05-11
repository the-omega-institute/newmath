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

def HolonomyTransportPacket [AskSetup] [PackageSetup]
    (bundleRow connectionRow loopRow endpoint curvatureLedger contLedger pkgRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundleRow ∧ UnaryHistory connectionRow ∧ UnaryHistory curvatureLedger ∧
    UnaryHistory contLedger ∧ Cont bundleRow connectionRow loopRow ∧
      Cont loopRow curvatureLedger endpoint ∧ Cont endpoint contLedger pkgRow ∧
        PkgSig bundle pkgRow pkg

theorem HolonomyTransportPacket_continuation_transport_stability [AskSetup] [PackageSetup]
    {bundleRow connectionRow loopRow endpoint curvatureLedger contLedger pkgRow bundleRow'
      connectionRow' loopRow' endpoint' curvatureLedger' contLedger' pkgRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundleRow connectionRow loopRow endpoint curvatureLedger contLedger
        pkgRow bundle pkg ->
      hsame bundleRow bundleRow' ->
        hsame connectionRow connectionRow' ->
          hsame curvatureLedger curvatureLedger' ->
            hsame contLedger contLedger' ->
              Cont bundleRow' connectionRow' loopRow' ->
                Cont loopRow' curvatureLedger' endpoint' ->
                  Cont endpoint' contLedger' pkgRow' ->
                    PkgSig bundle pkgRow' pkg ->
                      HolonomyTransportPacket bundleRow' connectionRow' loopRow' endpoint'
                          curvatureLedger' contLedger' pkgRow' bundle pkg ∧
                        hsame loopRow loopRow' ∧ hsame endpoint endpoint' ∧
                          hsame pkgRow pkgRow' := by
  intro packet sameBundle sameConnection sameCurvature sameCont loopRowRead endpointRead
    pkgRowRead pkgSig
  have bundleUnary' : UnaryHistory bundleRow' :=
    unary_transport packet.left sameBundle
  have connectionUnary' : UnaryHistory connectionRow' :=
    unary_transport packet.right.left sameConnection
  have curvatureUnary' : UnaryHistory curvatureLedger' :=
    unary_transport packet.right.right.left sameCurvature
  have contUnary' : UnaryHistory contLedger' :=
    unary_transport packet.right.right.right.left sameCont
  have sameLoop : hsame loopRow loopRow' :=
    cont_respects_hsame sameBundle sameConnection packet.right.right.right.right.left
      loopRowRead
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLoop sameCurvature packet.right.right.right.right.right.left
      endpointRead
  have samePkgRow : hsame pkgRow pkgRow' :=
    cont_respects_hsame sameEndpoint sameCont packet.right.right.right.right.right.right.left
      pkgRowRead
  exact And.intro
    (And.intro bundleUnary'
      (And.intro connectionUnary'
        (And.intro curvatureUnary'
          (And.intro contUnary'
            (And.intro loopRowRead
              (And.intro endpointRead (And.intro pkgRowRead pkgSig)))))))
    (And.intro sameLoop (And.intro sameEndpoint samePkgRow))

end BEDC.Derived.HolonomyUp
