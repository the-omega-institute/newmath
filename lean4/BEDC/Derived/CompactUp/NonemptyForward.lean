import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CompactFiniteRefinementChain_nonempty_forward
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
      (hsame finite BHist.Empty -> False) -> hsame finalFinite BHist.Empty -> False := by
  intro chain finiteNonempty
  induction chain with
  | base =>
      exact finiteNonempty
  | step prior extraCarrier finiteRel compactRel ih =>
      intro finalEmpty
      cases finiteRel
      have split := append_eq_empty_iff.mp finalEmpty
      exact ih split.left

end BEDC.Derived.CompactUp
