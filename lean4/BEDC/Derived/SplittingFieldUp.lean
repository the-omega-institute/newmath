import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SplittingFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SplittingFieldRootTransportPacket [AskSetup] [PackageSetup]
    (fieldext polynomial roots factors controw transport pkgrow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldext ∧ UnaryHistory polynomial ∧ UnaryHistory roots ∧
    UnaryHistory factors ∧ UnaryHistory transport ∧ Cont roots factors controw ∧
      Cont controw transport pkgrow ∧ PkgSig bundle pkgrow pkg

theorem SplittingFieldRootCarrierPacket_root_classifier_transport [AskSetup] [PackageSetup]
    {fieldext polynomial roots factors controw transport pkgrow roots' factors' controw'
      transport' pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootTransportPacket fieldext polynomial roots factors controw transport pkgrow
        bundle pkg ->
      hsame roots roots' ->
        hsame factors factors' ->
          hsame transport transport' ->
            Cont roots' factors' controw' ->
              Cont controw' transport' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  SplittingFieldRootTransportPacket fieldext polynomial roots' factors' controw'
                      transport' pkgrow' bundle pkg ∧
                    hsame controw controw' ∧ hsame pkgrow pkgrow' := by
  intro carrier sameRoots sameFactors sameTransport targetRootCont targetPkgCont targetPkgSig
  cases carrier with
  | intro fieldextUnary rest =>
      cases rest with
      | intro polynomialUnary rest =>
          cases rest with
          | intro rootsUnary rest =>
              cases rest with
              | intro factorsUnary rest =>
                  cases rest with
                  | intro transportUnary rest =>
                      cases rest with
                      | intro rootCont rest =>
                          cases rest with
                          | intro pkgCont _ =>
                              have rootsUnary' : UnaryHistory roots' :=
                                unary_transport rootsUnary sameRoots
                              have factorsUnary' : UnaryHistory factors' :=
                                unary_transport factorsUnary sameFactors
                              have transportUnary' : UnaryHistory transport' :=
                                unary_transport transportUnary sameTransport
                              have sameControw : hsame controw controw' :=
                                cont_respects_hsame sameRoots sameFactors rootCont targetRootCont
                              have samePkgrow : hsame pkgrow pkgrow' :=
                                cont_respects_hsame sameControw sameTransport pkgCont targetPkgCont
                              exact And.intro
                                (And.intro fieldextUnary
                                  (And.intro polynomialUnary
                                    (And.intro rootsUnary'
                                      (And.intro factorsUnary'
                                        (And.intro transportUnary'
                                          (And.intro targetRootCont
                                            (And.intro targetPkgCont targetPkgSig)))))))
                                (And.intro sameControw samePkgrow)

def SplittingFieldRootCarrierPacket [AskSetup] [PackageSetup]
    (fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldExt ∧ UnaryHistory polynomial ∧ UnaryHistory roots ∧
    UnaryHistory factors ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont fieldExt polynomial classifier ∧ Cont roots factors factorLedger ∧
        Cont provenance factorLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem SplittingFieldRootCarrierPacket_classifier_obligation [AskSetup] [PackageSetup]
    {fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldExt polynomial roots factors transport provenance
        classifier factorLedger endpoint bundle pkg ->
      UnaryHistory fieldExt ∧ UnaryHistory polynomial ∧ UnaryHistory roots ∧
        UnaryHistory factors ∧ UnaryHistory transport ∧ UnaryHistory classifier ∧
          Cont fieldExt polynomial classifier ∧ Cont roots factors factorLedger ∧
            hsame endpoint (append provenance factorLedger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have classifierRow : Cont fieldExt polynomial classifier :=
    packet.right.right.right.right.right.right.left
  have factorLedgerRow : Cont roots factors factorLedger :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance factorLedger endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed packet.left packet.right.left classifierRow
  have _factorLedgerUnary : UnaryHistory factorLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left factorLedgerRow
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro packet.right.right.right.right.left
            (And.intro classifierUnary
              (And.intro classifierRow
                (And.intro factorLedgerRow
                  (And.intro endpointRow
                    packet.right.right.right.right.right.right.right.right.right))))))))

theorem SplittingFieldRootCarrierPacket_root_downstream_threshold [AskSetup] [PackageSetup]
    {fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint
      pkgrow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldExt polynomial roots factors transport provenance
        classifier factorLedger endpoint bundle pkg ->
      Cont factorLedger transport pkgrow ->
        PkgSig bundle pkgrow pkg ->
          SplittingFieldRootTransportPacket fieldExt polynomial roots factors factorLedger transport
              pkgrow bundle pkg ∧
            Cont fieldExt polynomial classifier ∧ Cont roots factors factorLedger ∧
              Cont provenance factorLedger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet factorLedgerTransport pkgrowPkg
  have obligation := SplittingFieldRootCarrierPacket_classifier_obligation packet
  have transportPacket :
      SplittingFieldRootTransportPacket fieldExt polynomial roots factors factorLedger transport
        pkgrow bundle pkg :=
    And.intro obligation.left
      (And.intro obligation.right.left
        (And.intro obligation.right.right.left
          (And.intro obligation.right.right.right.left
            (And.intro obligation.right.right.right.right.left
              (And.intro obligation.right.right.right.right.right.right.right.left
                (And.intro factorLedgerTransport pkgrowPkg))))))
  exact And.intro transportPacket
    (And.intro obligation.right.right.right.right.right.right.left
      (And.intro obligation.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right)))

theorem SplittingFieldRootCarrierPacket_cyclotomic_consumer_source_boundary
    [AskSetup] [PackageSetup]
    {fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint
      pkgrow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldExt polynomial roots factors transport provenance
        classifier factorLedger endpoint bundle pkg ->
      Cont factorLedger transport pkgrow ->
        PkgSig bundle pkgrow pkg ->
          SplittingFieldRootTransportPacket fieldExt polynomial roots factors factorLedger
              transport pkgrow bundle pkg ∧
            Cont fieldExt polynomial classifier ∧ Cont roots factors factorLedger ∧
              Cont provenance factorLedger endpoint ∧ hsame factorLedger (append roots factors) ∧
                hsame pkgrow (append factorLedger transport) ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle pkgrow pkg := by
  intro packet factorLedgerTransport pkgrowPkg
  have downstream :=
    SplittingFieldRootCarrierPacket_root_downstream_threshold packet factorLedgerTransport
      pkgrowPkg
  exact And.intro downstream.left
    (And.intro downstream.right.left
      (And.intro downstream.right.right.left
        (And.intro downstream.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.left
            (And.intro factorLedgerTransport
              (And.intro downstream.right.right.right.right pkgrowPkg))))))

theorem SplittingFieldRootCarrierPacket_factor_ledger_exhaustion [AskSetup] [PackageSetup]
    {fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldExt polynomial roots factors transport provenance
        classifier factorLedger endpoint bundle pkg ->
      UnaryHistory factorLedger ∧ hsame factorLedger (append roots factors) ∧
        UnaryHistory endpoint ∧ hsame endpoint (append provenance factorLedger) ∧
          PkgSig bundle endpoint pkg := by
  intro packet
  have factorLedgerRow : Cont roots factors factorLedger :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance factorLedger endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have factorLedgerUnary : UnaryHistory factorLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left factorLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed packet.right.right.right.right.right.left factorLedgerUnary endpointRow
  exact And.intro factorLedgerUnary
    (And.intro factorLedgerRow
      (And.intro endpointUnary
        (And.intro endpointRow
          packet.right.right.right.right.right.right.right.right.right)))

theorem SplittingFieldRootCarrierPacket_root_ledger_obligation [AskSetup] [PackageSetup]
    {fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldExt polynomial roots factors transport provenance
        classifier factorLedger endpoint bundle pkg ->
      UnaryHistory factorLedger ∧ UnaryHistory endpoint ∧ Cont roots factors factorLedger ∧
        Cont provenance factorLedger endpoint ∧ hsame endpoint (append provenance factorLedger) ∧
          PkgSig bundle endpoint pkg := by
  intro packet
  have factorLedgerRow : Cont roots factors factorLedger :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance factorLedger endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have factorLedgerUnary : UnaryHistory factorLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left factorLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed packet.right.right.right.right.right.left factorLedgerUnary endpointRow
  exact And.intro factorLedgerUnary
    (And.intro endpointUnary
      (And.intro factorLedgerRow
        (And.intro endpointRow
          (And.intro endpointRow
            packet.right.right.right.right.right.right.right.right.right))))

theorem SplittingFieldRootCarrierPacket_ledger_obligation [AskSetup] [PackageSetup]
    {fieldExt polynomial roots factors transport provenance classifier factorLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldExt polynomial roots factors transport provenance
        classifier factorLedger endpoint bundle pkg ->
      UnaryHistory factorLedger ∧ hsame factorLedger (append roots factors) ∧
        hsame endpoint (append provenance factorLedger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have factorLedgerRow : Cont roots factors factorLedger :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance factorLedger endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have factorLedgerUnary : UnaryHistory factorLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left factorLedgerRow
  exact And.intro factorLedgerUnary
    (And.intro factorLedgerRow
      (And.intro endpointRow
        packet.right.right.right.right.right.right.right.right.right))

end BEDC.Derived.SplittingFieldUp
