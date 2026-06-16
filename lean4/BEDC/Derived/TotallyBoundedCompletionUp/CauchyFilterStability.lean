import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_cauchy_filter_stability [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName filterRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont net refinement filterRead ->
        Cont filterRead basis stableRead ->
          PkgSig bundle stableRead pkg ->
            UnaryHistory net ∧ UnaryHistory refinement ∧ UnaryHistory filterRead ∧
              UnaryHistory stableRead ∧ Cont source net refinement ∧
                Cont net refinement filterRead ∧ Cont filterRead basis stableRead ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle stableRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier netRefinementFilter filterBasisStable stableReadPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, _completionUnary, _extensionUnary,
    _transportUnary, sourceNetRefinement, _refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed netUnary refinementUnary netRefinementFilter
  have stableReadUnary : UnaryHistory stableRead :=
    unary_cont_closed filterReadUnary basisUnary filterBasisStable
  exact
    ⟨netUnary, refinementUnary, filterReadUnary, stableReadUnary, sourceNetRefinement,
      netRefinementFilter, filterBasisStable, localNamePkg, stableReadPkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
