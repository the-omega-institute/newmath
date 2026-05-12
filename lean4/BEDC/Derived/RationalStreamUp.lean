import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalStreamPacket [AskSetup] [PackageSetup]
    (index schedule rationalRows classifierRows transportRows routeRows provenance exportRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory rationalRows ∧
    UnaryHistory classifierRows ∧ UnaryHistory provenance ∧
      Cont index schedule transportRows ∧ Cont rationalRows classifierRows routeRows ∧
        Cont transportRows routeRows exportRow ∧ PkgSig bundle exportRow pkg

theorem RationalStreamPacket_schedule_transport_exactness [AskSetup] [PackageSetup]
    {index schedule rationalRows classifierRows transportRows routeRows provenance exportRow
      index' schedule' rationalRows' classifierRows' transportRows' routeRows' provenance'
      exportRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule rationalRows classifierRows transportRows routeRows
        provenance exportRow bundle pkg ->
      hsame index index' -> hsame schedule schedule' -> hsame rationalRows rationalRows' ->
        hsame classifierRows classifierRows' -> hsame provenance provenance' ->
          Cont index' schedule' transportRows' ->
            Cont rationalRows' classifierRows' routeRows' ->
              Cont transportRows' routeRows' exportRow' -> PkgSig bundle exportRow' pkg ->
                RationalStreamPacket index' schedule' rationalRows' classifierRows' transportRows'
                    routeRows' provenance' exportRow' bundle pkg ∧
                  hsame transportRows transportRows' ∧ hsame routeRows routeRows' ∧
                    hsame exportRow exportRow' := by
  intro packet sameIndex sameSchedule sameRationalRows sameClassifierRows sameProvenance
    transportedSchedule transportedClassifier transportedExport transportedPkg
  have sourceSchedule : Cont index schedule transportRows :=
    packet.right.right.right.right.right.left
  have sourceClassifier : Cont rationalRows classifierRows routeRows :=
    packet.right.right.right.right.right.right.left
  have sourceExport : Cont transportRows routeRows exportRow :=
    packet.right.right.right.right.right.right.right.left
  have sameTransportRows : hsame transportRows transportRows' :=
    cont_respects_hsame sameIndex sameSchedule sourceSchedule transportedSchedule
  have sameRouteRows : hsame routeRows routeRows' :=
    cont_respects_hsame sameRationalRows sameClassifierRows sourceClassifier transportedClassifier
  have sameExportRow : hsame exportRow exportRow' :=
    cont_respects_hsame sameTransportRows sameRouteRows sourceExport transportedExport
  have transportedPacket :
      RationalStreamPacket index' schedule' rationalRows' classifierRows' transportRows'
        routeRows' provenance' exportRow' bundle pkg :=
    ⟨unary_transport packet.left sameIndex,
      unary_transport packet.right.left sameSchedule,
      unary_transport packet.right.right.left sameRationalRows,
      unary_transport packet.right.right.right.left sameClassifierRows,
      unary_transport packet.right.right.right.right.left sameProvenance,
      transportedSchedule,
      transportedClassifier,
      transportedExport,
      transportedPkg⟩
  exact And.intro transportedPacket
    (And.intro sameTransportRows
      (And.intro sameRouteRows sameExportRow))

end BEDC.Derived.RationalStreamUp
