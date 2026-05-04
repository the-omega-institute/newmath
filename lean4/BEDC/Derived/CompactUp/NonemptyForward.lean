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

theorem CompactFiniteRefinementChain_compact_nonempty_forward
    {finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact ->
      (hsame compact BHist.Empty -> False) -> hsame finalCompact BHist.Empty -> False := by
  intro chain compactNonempty
  induction chain with
  | base =>
      exact compactNonempty
  | step prior extraCarrier finiteRel compactRel ih =>
      intro finalEmpty
      cases compactRel
      have split := append_eq_empty_iff.mp finalEmpty
      exact ih split.left

theorem CompactLocatedRefinementChain_located_nonempty_forward
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
      (hsame located BHist.Empty -> False) -> hsame finalLocated BHist.Empty -> False := by
  intro chain locatedNonempty
  induction chain with
  | base =>
      exact locatedNonempty
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      intro finalLocatedEmpty
      have locatedEmptyRel := cont_result_hsame_transport locatedRel finalLocatedEmpty
      exact ih (cont_empty_result_inversion locatedEmptyRel).left

theorem CompactLocatedRefinementChain_intermediate_nonempty_forward
    {finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact ->
      (hsame intermediate BHist.Empty -> False) -> hsame finalIntermediate BHist.Empty -> False := by
  intro chain intermediateNonempty
  induction chain with
  | base =>
      exact intermediateNonempty
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      intro finalIntermediateEmpty
      have intermediateEmptyRel :=
        cont_result_hsame_transport intermediateRel finalIntermediateEmpty
      exact ih (cont_empty_result_inversion intermediateEmptyRel).left

end BEDC.Derived.CompactUp
