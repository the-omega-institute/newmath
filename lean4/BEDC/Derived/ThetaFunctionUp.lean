import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ThetaFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ThetaFunctionCarrierSource [AskSetup] [PackageSetup]
    (period chart coeff provenance readback : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory period ∧ UnaryHistory chart ∧ UnaryHistory coeff ∧
    Cont period chart readback ∧ PkgSig bundle provenance pkg

def ThetaFunctionSourceClassifier [AskSetup] [PackageSetup]
    (period chart coeff provenance readback period' chart' coeff' provenance' readback' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ThetaFunctionCarrierSource period chart coeff provenance readback bundle pkg ∧
    ThetaFunctionCarrierSource period' chart' coeff' provenance' readback' bundle pkg ∧
      hsame period period' ∧ hsame chart chart' ∧ hsame coeff coeff' ∧
        hsame provenance provenance' ∧ hsame readback readback'

theorem ThetaFunctionCarrierSource_hsame_stability [AskSetup] [PackageSetup]
    {period chart coeff provenance readback period' chart' coeff' provenance' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ThetaFunctionCarrierSource period chart coeff provenance readback bundle pkg ->
      hsame period period' ->
        hsame chart chart' ->
          hsame coeff coeff' ->
            hsame provenance provenance' ->
              Cont period' chart' readback' ->
                PkgSig bundle provenance' pkg ->
                  ThetaFunctionCarrierSource period' chart' coeff' provenance' readback'
                      bundle pkg ∧
                    ThetaFunctionSourceClassifier period chart coeff provenance readback period'
                      chart' coeff' provenance' readback' bundle pkg ∧
                      hsame readback readback' := by
  intro carrier samePeriod sameChart sameCoeff sameProvenance readbackRow' pkgRow'
  have periodUnary' : UnaryHistory period' :=
    unary_transport carrier.left samePeriod
  have chartUnary' : UnaryHistory chart' :=
    unary_transport carrier.right.left sameChart
  have coeffUnary' : UnaryHistory coeff' :=
    unary_transport carrier.right.right.left sameCoeff
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame samePeriod sameChart carrier.right.right.right.left readbackRow'
  have carrier' :
      ThetaFunctionCarrierSource period' chart' coeff' provenance' readback' bundle pkg :=
    ⟨periodUnary', chartUnary', coeffUnary', readbackRow', pkgRow'⟩
  have classifier :
      ThetaFunctionSourceClassifier period chart coeff provenance readback period' chart' coeff'
        provenance' readback' bundle pkg :=
    ⟨carrier, carrier', samePeriod, sameChart, sameCoeff, sameProvenance, sameReadback⟩
  exact ⟨carrier', classifier, sameReadback⟩

end BEDC.Derived.ThetaFunctionUp
