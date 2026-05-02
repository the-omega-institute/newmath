import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactFiniteRefinementChain_prefix_closed
    {p finite compact finalFinite finalCompact : BHist} :
    CompactFiniteRefinementChain finite compact finalFinite finalCompact →
      CompactFiniteRefinementChain (append p finite) (append p compact) (append p finalFinite)
        (append p finalCompact) := by
  intro chain
  induction chain with
  | base =>
      exact CompactFiniteRefinementChain.base
  | step prior extraCarrier finiteRel compactRel ih =>
      apply CompactFiniteRefinementChain.step ih extraCarrier
      · apply cont_intro
        exact (congrArg (append p) finiteRel).trans (append_assoc p _ _).symm
      · apply cont_intro
        exact (congrArg (append p) compactRel).trans (append_assoc p _ _).symm

theorem CompactLocatedRefinementChain_prefix_closed
    {p finite located intermediate compact finalLocated finalIntermediate finalCompact : BHist} :
    CompactLocatedRefinementChain finite located intermediate compact finalLocated finalIntermediate
        finalCompact →
      CompactLocatedRefinementChain finite (append p located) (append p intermediate)
        (append p compact) (append p finalLocated) (append p finalIntermediate)
        (append p finalCompact) := by
  intro chain
  induction chain with
  | base =>
      exact CompactLocatedRefinementChain.base
  | step prior extraCarrier locatedRel intermediateRel compactRel ih =>
      apply CompactLocatedRefinementChain.step ih extraCarrier
      · apply cont_intro
        exact (congrArg (append p) locatedRel).trans (append_assoc p _ _).symm
      · apply cont_intro
        exact (congrArg (append p) intermediateRel).trans (append_assoc p _ _).symm
      · apply cont_intro
        exact (congrArg (append p) compactRel).trans (append_assoc p _ _).symm

end BEDC.Derived.CompactUp
