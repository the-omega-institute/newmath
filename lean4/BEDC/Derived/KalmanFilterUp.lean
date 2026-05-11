import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KalmanFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KalmanFilterCarrier [AskSetup] [PackageSetup]
    (prior transition prediction observation residual covariance gain posterior innovation update
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧
    UnaryHistory transition ∧
      UnaryHistory prediction ∧
        UnaryHistory observation ∧
          UnaryHistory residual ∧
            UnaryHistory covariance ∧
              UnaryHistory gain ∧
                UnaryHistory posterior ∧
                  UnaryHistory innovation ∧
                    UnaryHistory update ∧
                      UnaryHistory provenance ∧
                        UnaryHistory endpoint ∧
                          Cont prior transition prediction ∧
                            Cont prediction observation residual ∧
                              Cont covariance observation innovation ∧
                                Cont innovation gain update ∧
                                  Cont update posterior endpoint ∧
                                    Cont endpoint provenance endpoint ∧
                                      PkgSig bundle endpoint pkg

theorem KalmanFilterCarrier_prediction_update_obligation [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update provenance endpoint bundle pkg ->
      Cont prior transition prediction ∧
        Cont prediction observation residual ∧
          Cont covariance observation innovation ∧
            Cont innovation gain update ∧
              Cont update posterior endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact And.intro carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
    (And.intro
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      (And.intro
        carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
        (And.intro
          carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
          (And.intro
            carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
            carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.KalmanFilterUp
