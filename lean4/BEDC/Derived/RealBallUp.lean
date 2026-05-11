import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealBallUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def RealBallWindowCarrier [AskSetup] [PackageSetup]
    (center radius window provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory provenance ∧
    Cont center radius window ∧ Cont window provenance ledger ∧ PkgSig bundle ledger pkg

theorem RealBallWindowCarrier_metric_neighborhood_handoff [AskSetup] [PackageSetup]
    {center radius window provenance ledger metricRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealBallWindowCarrier center radius window provenance ledger bundle pkg ->
      Cont ledger radius metricRow ->
        PkgSig bundle metricRow pkg ->
          UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory window ∧
            UnaryHistory metricRow ∧ hsame window (append center radius) ∧
              hsame metricRow (append ledger radius) ∧ PkgSig bundle metricRow pkg := by
  intro carrier metricRoute metricPkg
  have centerUnary : UnaryHistory center :=
    carrier.left
  have radiusUnary : UnaryHistory radius :=
    carrier.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.left
  have windowRoute : Cont center radius window :=
    carrier.right.right.right.left
  have ledgerRoute : Cont window provenance ledger :=
    carrier.right.right.right.right.left
  have windowUnary : UnaryHistory window :=
    unary_cont_closed centerUnary radiusUnary windowRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed windowUnary provenanceUnary ledgerRoute
  have metricUnary : UnaryHistory metricRow :=
    unary_cont_closed ledgerUnary radiusUnary metricRoute
  exact And.intro centerUnary
    (And.intro radiusUnary
      (And.intro windowUnary
        (And.intro metricUnary
          (And.intro windowRoute
            (And.intro metricRoute metricPkg)))))

def RealBallWindowPacket [AskSetup] [PackageSetup]
    (center radius window provenance ledger : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ PositiveUnaryDenominator radius ∧ UnaryHistory window ∧
    UnaryHistory provenance ∧ UnaryHistory ledger ∧ Cont center radius window ∧
      Cont window provenance ledger ∧ PkgSig bundle ledger pkg

theorem RealBallWindowPacket_radius_transport [AskSetup] [PackageSetup]
    {center radius window provenance ledger center' radius' window' provenance' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealBallWindowPacket center radius window provenance ledger bundle pkg ->
      hsame center center' ->
        hsame radius radius' ->
          hsame window window' ->
            hsame provenance provenance' ->
              Cont center' radius' window' ->
                Cont window' provenance' ledger' ->
                  PkgSig bundle ledger' pkg ->
                    RealBallWindowPacket center' radius' window' provenance' ledger'
                        bundle pkg ∧
                      hsame ledger ledger' ∧ hsame window' (append center' radius') ∧
                        hsame ledger' (append window' provenance') := by
  intro packet sameCenter sameRadius sameWindow sameProvenance windowRow' ledgerRow'
    ledgerPkg'
  obtain ⟨centerUnary, radiusPositive, _windowUnary, provenanceUnary, _ledgerUnary,
    _windowRow, ledgerRow, _ledgerPkg⟩ := packet
  have centerUnary' : UnaryHistory center' :=
    unary_transport centerUnary sameCenter
  have radiusPositive' : PositiveUnaryDenominator radius' :=
    PositiveUnaryDenominator_hsame_transport sameRadius radiusPositive
  have radiusUnary' : UnaryHistory radius' :=
    (PositiveUnaryDenominator_unary_and_nonempty radiusPositive').left
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed centerUnary' radiusUnary' windowRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed windowUnary' provenanceUnary' ledgerRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameWindow sameProvenance ledgerRow ledgerRow'
  exact
    And.intro
      (And.intro centerUnary'
        (And.intro radiusPositive'
          (And.intro windowUnary'
            (And.intro provenanceUnary'
              (And.intro ledgerUnary'
                (And.intro windowRow' (And.intro ledgerRow' ledgerPkg')))))))
      (And.intro sameLedger (And.intro windowRow' ledgerRow'))

end BEDC.Derived.RealBallUp
