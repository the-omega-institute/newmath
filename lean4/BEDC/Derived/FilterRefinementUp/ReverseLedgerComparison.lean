import BEDC.Derived.FilterRefinementUp.CauchyPreservation

namespace BEDC.Derived.FilterRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterRefinementCarrier_reverse_ledger_comparison [AskSetup] [PackageSetup]
    {source refined base completion transport replay provenance localName reverseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterRefinementCarrier source refined base completion transport replay provenance localName
        bundle pkg →
      Cont refined base reverseRead →
        PkgSig bundle reverseRead pkg →
          UnaryHistory refined ∧ UnaryHistory base ∧ UnaryHistory reverseRead ∧
            Cont refined base reverseRead ∧ PkgSig bundle reverseRead pkg := by
  -- BEDC touchpoint anchor: FilterRefinementCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier reverseRoute reversePkg
  obtain ⟨_sourceUnary, refinedUnary, baseUnary, _completionUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _refinedBaseSource,
    _sourceCompletionReplay, _transportReplayLocalName, _provenancePkg,
    _localNamePkg⟩ := carrier
  have reverseUnary : UnaryHistory reverseRead :=
    unary_cont_closed refinedUnary baseUnary reverseRoute
  exact ⟨refinedUnary, baseUnary, reverseUnary, reverseRoute, reversePkg⟩

end BEDC.Derived.FilterRefinementUp
