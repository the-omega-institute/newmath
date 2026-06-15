import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TotallyBoundedCompletionCarrier [AskSetup] [PackageSetup]
    (source net refinement basis embedding completion separated extension transport provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory net ∧ UnaryHistory basis ∧
    UnaryHistory completion ∧ UnaryHistory extension ∧ UnaryHistory transport ∧
      Cont source net refinement ∧ Cont refinement basis embedding ∧
        Cont embedding completion separated ∧ Cont separated extension provenance ∧
          Cont transport provenance localName ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem TotallyBoundedCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      UnaryHistory source ∧ UnaryHistory net ∧ UnaryHistory refinement ∧
        UnaryHistory basis ∧ UnaryHistory embedding ∧ UnaryHistory completion ∧
          UnaryHistory separated ∧ UnaryHistory extension ∧ UnaryHistory transport ∧
            UnaryHistory provenance ∧ UnaryHistory localName ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary, transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    separatedExtensionProvenance, transportProvenanceLocalName, _provenancePkg,
    localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionProvenance
  have localNameUnary : UnaryHistory localName :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceLocalName
  exact
    ⟨sourceUnary, netUnary, refinementUnary, basisUnary, embeddingUnary, completionUnary,
      separatedUnary, extensionUnary, transportUnary, provenanceUnary, localNameUnary,
      localNamePkg⟩

theorem TotallyBoundedCompletionCarrier_refinement_ledger_obligation [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net refinement ∧ Cont refinement basis embedding ∧
        Cont embedding completion separated ∧ UnaryHistory refinement ∧ UnaryHistory embedding ∧
          UnaryHistory separated ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, _extensionUnary, _transportUnary,
    sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
    _separatedExtensionProvenance, _transportProvenanceLocalName, _provenancePkg,
    localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  exact
    ⟨sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
      refinementUnary, embeddingUnary, separatedUnary, localNamePkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
