import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionFiniteNetCompletionRoute [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName finiteNetRead completionRead extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net finiteNetRead ->
        Cont embedding completion completionRead ->
          Cont separated extension extensionRead ->
            PkgSig bundle finiteNetRead pkg ->
              PkgSig bundle completionRead pkg ->
                PkgSig bundle extensionRead pkg ->
                  UnaryHistory source ∧ UnaryHistory net ∧ UnaryHistory refinement ∧
                    UnaryHistory basis ∧ UnaryHistory embedding ∧
                      UnaryHistory completion ∧ UnaryHistory separated ∧
                        UnaryHistory extension ∧ UnaryHistory finiteNetRead ∧
                          UnaryHistory completionRead ∧ UnaryHistory extensionRead ∧
                            Cont source net refinement ∧ Cont refinement basis embedding ∧
                              Cont embedding completion separated ∧
                                Cont source net finiteNetRead ∧
                                  Cont embedding completion completionRead ∧
                                    Cont separated extension extensionRead ∧
                                      PkgSig bundle localName pkg ∧
                                        PkgSig bundle finiteNetRead pkg ∧
                                          PkgSig bundle completionRead pkg ∧
                                            PkgSig bundle extensionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier finiteNetRoute completionRoute extensionRoute finiteNetPkg completionPkg
    extensionPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary,
    _transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed sourceUnary netUnary finiteNetRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed embeddingUnary completionUnary completionRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed separatedUnary extensionUnary extensionRoute
  exact
    ⟨sourceUnary, netUnary, refinementUnary, basisUnary, embeddingUnary, completionUnary,
      separatedUnary, extensionUnary, finiteNetUnary, completionReadUnary, extensionReadUnary,
      sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
      finiteNetRoute, completionRoute, extensionRoute, localNamePkg, finiteNetPkg,
      completionPkg, extensionPkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
