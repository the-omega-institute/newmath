import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem TotallyBoundedCompletionCarrier_obligation_ledger [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont source net refinement ∧ Cont refinement basis embedding ∧
        Cont embedding completion separated ∧ Cont separated extension provenance ∧
          Cont transport provenance localName ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro carrier
  obtain ⟨_sourceUnary, _netUnary, _basisUnary, _completionUnary, _extensionUnary,
    _transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    embeddingCompletionSeparated, separatedExtensionProvenance,
    transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
      separatedExtensionProvenance, transportProvenanceLocalName, localNamePkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
