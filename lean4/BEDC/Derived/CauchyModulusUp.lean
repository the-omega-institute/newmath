import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusCarrier [AskSetup] [PackageSetup]
    (precision threshold tolerance schedule consumption provenance window : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory tolerance ∧
    UnaryHistory schedule ∧ UnaryHistory consumption ∧ UnaryHistory provenance ∧
      UnaryHistory window ∧ Cont precision threshold consumption ∧
        Cont tolerance schedule provenance ∧ Cont consumption provenance window ∧
          PkgSig bundle window pkg

theorem CauchyModulusCarrier_hsame_stability [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule consumption provenance window precision' threshold'
      tolerance' schedule' consumption' provenance' window' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusCarrier precision threshold tolerance schedule consumption provenance window
        bundle pkg ->
      hsame precision precision' ->
        hsame threshold threshold' ->
          hsame tolerance tolerance' ->
            hsame schedule schedule' ->
              Cont precision' threshold' consumption' ->
                Cont tolerance' schedule' provenance' ->
                  Cont consumption' provenance' window' ->
                    PkgSig bundle window' pkg ->
                      CauchyModulusCarrier precision' threshold' tolerance' schedule'
                          consumption' provenance' window' bundle pkg ∧
                        hsame consumption consumption' ∧ hsame provenance provenance' ∧
                          hsame window window' := by
  intro carrier samePrecision sameThreshold sameTolerance sameSchedule consumptionRow'
    provenanceRow' windowRow' pkgSig'
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport carrier.left samePrecision
  have thresholdUnary' : UnaryHistory threshold' :=
    unary_transport carrier.right.left sameThreshold
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport carrier.right.right.left sameTolerance
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport carrier.right.right.right.left sameSchedule
  have consumptionUnary' : UnaryHistory consumption' :=
    unary_cont_closed precisionUnary' thresholdUnary' consumptionRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed toleranceUnary' scheduleUnary' provenanceRow'
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed consumptionUnary' provenanceUnary' windowRow'
  have sameConsumption : hsame consumption consumption' :=
    cont_respects_hsame samePrecision sameThreshold
      carrier.right.right.right.right.right.right.right.left consumptionRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTolerance sameSchedule
      carrier.right.right.right.right.right.right.right.right.left provenanceRow'
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameConsumption sameProvenance
      carrier.right.right.right.right.right.right.right.right.right.left windowRow'
  constructor
  · exact
      And.intro precisionUnary'
        (And.intro thresholdUnary'
          (And.intro toleranceUnary'
            (And.intro scheduleUnary'
              (And.intro consumptionUnary'
                (And.intro provenanceUnary'
                  (And.intro windowUnary'
                    (And.intro consumptionRow'
                      (And.intro provenanceRow'
                        (And.intro windowRow' pkgSig')))))))))
  · exact And.intro sameConsumption (And.intro sameProvenance sameWindow)

end BEDC.Derived.CauchyModulusUp
