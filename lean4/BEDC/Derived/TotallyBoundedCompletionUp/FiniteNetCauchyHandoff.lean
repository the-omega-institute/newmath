import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionFiniteNetCauchyHandoff [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName netRead refinedRead basisRead embeddingRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont source net netRead →
        Cont netRead refinement refinedRead →
          Cont refinedRead basis basisRead →
            Cont basisRead embedding embeddingRead →
              Cont embeddingRead completion completionRead →
                PkgSig bundle completionRead pkg →
                  UnaryHistory netRead ∧ UnaryHistory refinedRead ∧ UnaryHistory basisRead ∧
                    UnaryHistory embeddingRead ∧ UnaryHistory completionRead ∧
                      Cont source net netRead ∧ Cont netRead refinement refinedRead ∧
                        Cont refinedRead basis basisRead ∧
                          Cont basisRead embedding embeddingRead ∧
                            Cont embeddingRead completion completionRead ∧
                              PkgSig bundle localName pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: TotallyBoundedCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceNetRead netRefinedRead refinedBasisRead basisEmbeddingRead
    embeddingCompletionRead completionPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, _extensionUnary,
    _transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed netReadUnary refinementUnary netRefinedRead
  have basisReadUnary : UnaryHistory basisRead :=
    unary_cont_closed refinedReadUnary basisUnary refinedBasisRead
  have embeddingReadUnary : UnaryHistory embeddingRead :=
    unary_cont_closed basisReadUnary embeddingUnary basisEmbeddingRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed embeddingReadUnary completionUnary embeddingCompletionRead
  exact
    ⟨netReadUnary, refinedReadUnary, basisReadUnary, embeddingReadUnary, completionReadUnary,
      sourceNetRead, netRefinedRead, refinedBasisRead, basisEmbeddingRead,
      embeddingCompletionRead, localNamePkg, completionPkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
