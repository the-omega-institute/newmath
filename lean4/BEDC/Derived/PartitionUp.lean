import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PartitionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PartitionBHistCarrier [AskSetup] [PackageSetup]
    (listRow partRows sumRow weakDecrease youngBoundary route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory listRow ∧ UnaryHistory partRows ∧ UnaryHistory sumRow ∧
    UnaryHistory weakDecrease ∧ Cont listRow partRows route ∧
      Cont route sumRow youngBoundary ∧ Cont youngBoundary weakDecrease endpoint ∧
        PkgSig bundle endpoint pkg

theorem PartitionBHistCarrier_classifier_stability [AskSetup] [PackageSetup]
    {listRow partRows sumRow weakDecrease youngBoundary route endpoint listRow' partRows'
      sumRow' weakDecrease' youngBoundary' route' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow weakDecrease youngBoundary route endpoint
        bundle pkg ->
      hsame listRow listRow' ->
        hsame partRows partRows' ->
          hsame sumRow sumRow' ->
            hsame weakDecrease weakDecrease' ->
              Cont listRow' partRows' route' ->
                Cont route' sumRow' youngBoundary' ->
                  Cont youngBoundary' weakDecrease' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      PartitionBHistCarrier listRow' partRows' sumRow' weakDecrease'
                          youngBoundary' route' endpoint' bundle pkg ∧
                        hsame endpoint endpoint' := by
  intro carrier sameList sameParts sameSum sameWeak routeCont' youngBoundaryCont'
    endpointCont' endpointPkg'
  have routeSame : hsame route route' :=
    cont_respects_hsame sameList sameParts carrier.right.right.right.right.left routeCont'
  have youngBoundarySame : hsame youngBoundary youngBoundary' :=
    cont_respects_hsame routeSame sameSum carrier.right.right.right.right.right.left
      youngBoundaryCont'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame youngBoundarySame sameWeak
      carrier.right.right.right.right.right.right.left endpointCont'
  have transportedCarrier :
      PartitionBHistCarrier listRow' partRows' sumRow' weakDecrease' youngBoundary' route'
        endpoint' bundle pkg :=
    And.intro (unary_transport carrier.left sameList)
      (And.intro (unary_transport carrier.right.left sameParts)
        (And.intro (unary_transport carrier.right.right.left sameSum)
          (And.intro (unary_transport carrier.right.right.right.left sameWeak)
            (And.intro routeCont'
              (And.intro youngBoundaryCont' (And.intro endpointCont' endpointPkg'))))))
  exact And.intro transportedCarrier endpointSame

end BEDC.Derived.PartitionUp
