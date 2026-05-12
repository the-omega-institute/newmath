import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformContinuityPacket [AskSetup] [PackageSetup]
    (sourceMetric targetMetric graph tolerance bundleRow centers pointwise cover lowerBound
      triangle transport nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceMetric ∧ UnaryHistory targetMetric ∧ UnaryHistory graph ∧
    UnaryHistory tolerance ∧ UnaryHistory bundleRow ∧ UnaryHistory centers ∧
      UnaryHistory pointwise ∧ UnaryHistory cover ∧ UnaryHistory lowerBound ∧
        UnaryHistory triangle ∧ UnaryHistory transport ∧ UnaryHistory nameRow ∧
          Cont bundleRow centers pointwise ∧ Cont cover lowerBound triangle ∧
            Cont triangle transport nameRow ∧ PkgSig bundle nameRow pkg

theorem UniformContinuityPacket_finite_net_modulus_fold [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph tolerance bundleRow centers pointwise cover lowerBound
      triangle transport nameRow folded : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformContinuityPacket sourceMetric targetMetric graph tolerance bundleRow centers pointwise
        cover lowerBound triangle transport nameRow bundle pkg ->
      Cont bundleRow pointwise folded ->
        Cont lowerBound folded tolerance ->
          UnaryHistory bundleRow ∧ UnaryHistory pointwise ∧ UnaryHistory folded ∧
            Cont bundleRow pointwise folded ∧ Cont lowerBound folded tolerance := by
  intro packet foldRoute toleranceRoute
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _toleranceUnary,
    bundleRowUnary, _centersUnary, pointwiseUnary, _coverUnary, lowerBoundUnary,
    _triangleUnary, _transportUnary, _nameRowUnary, _bundlePointwiseRoute,
    _triangleRoute, _nameRowRoute, _nameRowPkg⟩ := packet
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed bundleRowUnary pointwiseUnary foldRoute
  have _toleranceFromFold : UnaryHistory tolerance :=
    unary_cont_closed lowerBoundUnary foldedUnary toleranceRoute
  exact ⟨bundleRowUnary, pointwiseUnary, foldedUnary, foldRoute, toleranceRoute⟩

end BEDC.Derived.UniformContinuityUp
