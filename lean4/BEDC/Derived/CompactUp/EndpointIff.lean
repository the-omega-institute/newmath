import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist

theorem CompactFiniteRefinementChain_endpoint_hsame_iff
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
      (hsame finalFinite finalCompact ↔ hsame finite compact) := by
  intro chain
  exact Iff.intro (CompactFiniteRefinementChain_endpoint_hsame_reflects chain)
    (CompactFiniteRefinementChain_endpoint_hsame chain)

end BEDC.Derived.CompactUp
