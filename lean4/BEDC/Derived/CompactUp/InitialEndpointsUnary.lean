import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompactFiniteRefinementChain_initial_endpoints_unary
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact →
      UnaryHistory finalFinite → UnaryHistory finalCompact →
        UnaryHistory finite ∧ UnaryHistory compact := by
  intro chain finalFiniteCarrier finalCompactCarrier
  induction chain with
  | base =>
      exact And.intro finalFiniteCarrier finalCompactCarrier
  | step prior extraCarrier finiteRel compactRel ih =>
      exact ih
        (unary_cont_left_factor finiteRel finalFiniteCarrier)
        (unary_cont_left_factor compactRel finalCompactCarrier)

theorem CompactLocatedRefinementChain_initial_endpoints_unary
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact →
      UnaryHistory finalLocated → UnaryHistory finalIntermediate →
        UnaryHistory located ∧ UnaryHistory intermediate := by
  intro chain finalLocatedCarrier finalIntermediateCarrier
  induction chain with
  | base =>
      exact And.intro finalLocatedCarrier finalIntermediateCarrier
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      exact ih
        (unary_cont_left_factor locatedRel finalLocatedCarrier)
        (unary_cont_left_factor intermediateRel finalIntermediateCarrier)

theorem CompactLocatedRefinementChain_initial_located_intermediate_unary
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact →
      UnaryHistory finalLocated → UnaryHistory finalIntermediate →
        UnaryHistory located ∧ UnaryHistory intermediate := by
  exact CompactLocatedRefinementChain_initial_endpoints_unary

end BEDC.Derived.CompactUp
