import BEDC.Derived.DistributionUp
import BEDC.Derived.RiemannianMetricUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FisherInfoUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.DistributionUp
open BEDC.Derived.RiemannianMetricUp

def FisherInfoBHistScoreCarrier [AskSetup] [PackageSetup]
    (distribution metric parameter score expectation component provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  DistributionPushforwardSourceSpec distribution ∧
    RiemannianMetricSingletonFibreSurface parameter score metric ∧
      UnaryHistory parameter ∧ UnaryHistory score ∧
        Cont distribution score expectation ∧ Cont expectation metric component ∧
          PkgSig bundle provenance pkg ∧ Cont component provenance ledger

theorem FisherInfoBHistScoreCarrier_distribution_source_obligation [AskSetup] [PackageSetup]
    {distribution metric parameter score expectation component provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FisherInfoBHistScoreCarrier distribution metric parameter score expectation component
        provenance ledger bundle pkg ->
      DistributionPushforwardSourceSpec distribution ∧ UnaryHistory parameter ∧
        UnaryHistory score ∧ Cont distribution score expectation ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  exact And.intro carrier.left
    (And.intro carrier.right.right.left
      (And.intro carrier.right.right.right.left
        (And.intro carrier.right.right.right.right.left
          carrier.right.right.right.right.right.right.left)))

end BEDC.Derived.FisherInfoUp
