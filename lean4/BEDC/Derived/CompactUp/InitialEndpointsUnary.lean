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

end BEDC.Derived.CompactUp
