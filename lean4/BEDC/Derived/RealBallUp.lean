import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealBallWindowCarrier [AskSetup] [PackageSetup]
    (center radius window provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory window ∧ UnaryHistory provenance ∧
    UnaryHistory ledger ∧ Cont center radius window ∧ Cont window provenance ledger ∧
      PkgSig bundle ledger pkg

theorem RealBallWindowCarrier_radius_transport [AskSetup] [PackageSetup]
    {center radius window provenance ledger center' radius' window' provenance' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealBallWindowCarrier center radius window provenance ledger bundle pkg ->
      hsame center center' ->
        hsame radius radius' ->
          hsame window window' ->
            hsame provenance provenance' ->
              Cont center' radius' window' ->
                Cont window' provenance' ledger' ->
                  PkgSig bundle ledger' pkg ->
                    RealBallWindowCarrier center' radius' window' provenance' ledger' bundle pkg ∧
                      hsame ledger ledger' := by
  intro carrier sameCenter sameRadius sameWindow sameProvenance windowCont' ledgerCont'
    ledgerPkg'
  obtain ⟨centerUnary, radiusUnary, _windowUnary, provenanceUnary, _ledgerUnary, windowCont,
    ledgerCont, _ledgerPkg⟩ := carrier
  have centerUnary' : UnaryHistory center' :=
    unary_transport centerUnary sameCenter
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed centerUnary' radiusUnary' windowCont'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed windowUnary' provenanceUnary' ledgerCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameWindow sameProvenance ledgerCont ledgerCont'
  exact
    And.intro
      (And.intro centerUnary'
        (And.intro radiusUnary'
          (And.intro windowUnary'
            (And.intro provenanceUnary'
              (And.intro ledgerUnary'
                (And.intro windowCont'
                  (And.intro ledgerCont' ledgerPkg')))))))
      sameLedger

end BEDC.Derived.RealBallUp
