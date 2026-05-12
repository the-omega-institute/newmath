import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ComputableRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ComputableRealSourcePacket [AskSetup] [PackageSetup]
    (stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
    UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
      Cont transport routes provenance ∧ Cont provenance name endpoint ∧
        PkgSig bundle endpoint pkg

theorem ComputableRealSourcePacket_ledger_coverage [AskSetup] [PackageSetup]
    {stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSourcePacket stream modulus dyadic regseq «seal» transport routes provenance
        name endpoint bundle pkg ->
      UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
        UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
          Cont transport routes provenance ∧ Cont provenance name endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact packet.left
  · constructor
    · exact packet.right.left
    · constructor
      · exact packet.right.right.left
      · constructor
        · exact packet.right.right.right.left
        · constructor
          · exact packet.right.right.right.right.left
          · constructor
            · exact packet.right.right.right.right.right.left
            · constructor
              · exact packet.right.right.right.right.right.right.left
              · constructor
                · exact packet.right.right.right.right.right.right.right.left
                · constructor
                  · exact packet.right.right.right.right.right.right.right.right.left
                  · exact packet.right.right.right.right.right.right.right.right.right

def ComputableRealSource [AskSetup] [PackageSetup]
    (schedule modulus dyadic regularity realSeal transportRows routeRows provenance
      exportRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
    UnaryHistory regularity ∧ UnaryHistory realSeal ∧ UnaryHistory provenance ∧
      Cont schedule modulus transportRows ∧ Cont dyadic regularity routeRows ∧
        Cont transportRows routeRows exportRow ∧ PkgSig bundle exportRow pkg

theorem ComputableRealSource_classifier_transport [AskSetup] [PackageSetup]
    {schedule modulus dyadic regularity realSeal transportRows routeRows provenance exportRow
      schedule' modulus' dyadic' regularity' realSeal' transportRows' routeRows' provenance'
      exportRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSource schedule modulus dyadic regularity realSeal transportRows routeRows
        provenance exportRow bundle pkg ->
      hsame schedule schedule' -> hsame modulus modulus' -> hsame dyadic dyadic' ->
        hsame regularity regularity' -> hsame realSeal realSeal' -> hsame provenance provenance' ->
          Cont schedule' modulus' transportRows' ->
            Cont dyadic' regularity' routeRows' ->
              Cont transportRows' routeRows' exportRow' -> PkgSig bundle exportRow' pkg ->
                ComputableRealSource schedule' modulus' dyadic' regularity' realSeal' transportRows'
                    routeRows' provenance' exportRow' bundle pkg ∧
                  hsame transportRows transportRows' ∧ hsame routeRows routeRows' ∧
                    hsame exportRow exportRow' := by
  intro source sameSchedule sameModulus sameDyadic sameRegularity sameRealSeal sameProvenance
    transportedSchedule transportedClassifier transportedExport transportedPkg
  have sourceSchedule : Cont schedule modulus transportRows :=
    source.right.right.right.right.right.right.left
  have sourceClassifier : Cont dyadic regularity routeRows :=
    source.right.right.right.right.right.right.right.left
  have sourceExport : Cont transportRows routeRows exportRow :=
    source.right.right.right.right.right.right.right.right.left
  have sameTransportRows : hsame transportRows transportRows' :=
    cont_respects_hsame sameSchedule sameModulus sourceSchedule transportedSchedule
  have sameRouteRows : hsame routeRows routeRows' :=
    cont_respects_hsame sameDyadic sameRegularity sourceClassifier transportedClassifier
  have sameExportRow : hsame exportRow exportRow' :=
    cont_respects_hsame sameTransportRows sameRouteRows sourceExport transportedExport
  have transportedSource :
      ComputableRealSource schedule' modulus' dyadic' regularity' realSeal' transportRows'
        routeRows' provenance' exportRow' bundle pkg :=
    ⟨unary_transport source.left sameSchedule,
      unary_transport source.right.left sameModulus,
      unary_transport source.right.right.left sameDyadic,
      unary_transport source.right.right.right.left sameRegularity,
      unary_transport source.right.right.right.right.left sameRealSeal,
      unary_transport source.right.right.right.right.right.left sameProvenance,
      transportedSchedule,
      transportedClassifier,
      transportedExport,
      transportedPkg⟩
  exact And.intro transportedSource
    (And.intro sameTransportRows
      (And.intro sameRouteRows sameExportRow))

end BEDC.Derived.ComputableRealUp
