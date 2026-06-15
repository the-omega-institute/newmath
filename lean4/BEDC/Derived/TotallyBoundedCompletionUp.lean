import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem TotallyBoundedCompletionCarrier_cauchy_filter_basis_handoff [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont net refinement basisRead →
        PkgSig bundle basisRead pkg →
          UnaryHistory net ∧ UnaryHistory refinement ∧ UnaryHistory basis ∧
            UnaryHistory basisRead ∧ Cont source net refinement ∧
              Cont refinement basis embedding ∧ Cont net refinement basisRead ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle basisRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier netRefinementBasis basisReadPkg
  obtain ⟨_sourceUnary, netUnary, basisUnary, _completionUnary, _extensionUnary,
    _transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed _sourceUnary netUnary sourceNetRefinement
  have basisReadUnary : UnaryHistory basisRead :=
    unary_cont_closed netUnary refinementUnary netRefinementBasis
  exact
    ⟨netUnary, refinementUnary, basisUnary, basisReadUnary, sourceNetRefinement,
      refinementBasisEmbedding, netRefinementBasis, localNamePkg, basisReadPkg⟩

theorem TotallyBoundedCompletionCarrier_separated_extension_obligation [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont separated extension separatedRead ->
        PkgSig bundle separatedRead pkg ->
          UnaryHistory separated ∧ UnaryHistory extension ∧ UnaryHistory provenance ∧
            UnaryHistory separatedRead ∧ Cont embedding completion separated ∧
              Cont separated extension provenance ∧ Cont separated extension separatedRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle separatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier separatedExtensionRead separatedReadPkg
  obtain ⟨sourceUnary, netUnary, basisUnary, completionUnary, extensionUnary,
    _transportUnary, sourceNetRefinement, refinementBasisEmbedding,
    embeddingCompletionSeparated, separatedExtensionProvenance,
    _transportProvenanceLocalName, provenancePkg, _localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have embeddingUnary : UnaryHistory embedding :=
    unary_cont_closed refinementUnary basisUnary refinementBasisEmbedding
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed embeddingUnary completionUnary embeddingCompletionSeparated
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionProvenance
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionRead
  exact
    ⟨separatedUnary, extensionUnary, provenanceUnary, separatedReadUnary,
      embeddingCompletionSeparated, separatedExtensionProvenance, separatedExtensionRead,
      provenancePkg, separatedReadPkg⟩

theorem TotallyBoundedCompletionCarrier_net_handoff [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName netRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net netRead ->
        UnaryHistory source ∧ UnaryHistory net ∧ UnaryHistory refinement ∧
          UnaryHistory netRead ∧ Cont source net refinement ∧ Cont source net netRead ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceNetRead
  obtain ⟨sourceUnary, netUnary, _basisUnary, _completionUnary, _extensionUnary,
    _transportUnary, sourceNetRefinement, _refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  exact
    ⟨sourceUnary, netUnary, refinementUnary, netReadUnary, sourceNetRefinement,
      sourceNetRead, localNamePkg⟩

theorem TotallyBoundedCompletionCarrier_extension_nonescape [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont separated extension extensionRead ->
        PkgSig bundle extensionRead pkg ->
          UnaryHistory source ∧ UnaryHistory net ∧ UnaryHistory refinement ∧
            UnaryHistory basis ∧ UnaryHistory embedding ∧ UnaryHistory completion ∧
              UnaryHistory separated ∧ UnaryHistory extension ∧ UnaryHistory extensionRead ∧
                Cont source net refinement ∧ Cont refinement basis embedding ∧
                  Cont embedding completion separated ∧ Cont separated extension extensionRead ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle extensionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier separatedExtensionRead extensionReadPkg
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
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionRead
  exact
    ⟨sourceUnary, netUnary, refinementUnary, basisUnary, embeddingUnary, completionUnary,
      separatedUnary, extensionUnary, extensionReadUnary, sourceNetRefinement,
      refinementBasisEmbedding, embeddingCompletionSeparated, separatedExtensionRead,
      localNamePkg, extensionReadPkg⟩

theorem TotallyBoundedCompletionCarrier_net_refinement_stability [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName refinementRead embeddingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont net refinement refinementRead ->
        Cont refinement basis embeddingRead ->
          PkgSig bundle localName pkg ->
            UnaryHistory net ∧ UnaryHistory refinement ∧ UnaryHistory refinementRead ∧
              UnaryHistory embeddingRead ∧ Cont source net refinement ∧
                Cont net refinement refinementRead ∧ Cont refinement basis embeddingRead ∧
                  PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier netRefinementRead refinementBasisRead localNamePkg
  obtain ⟨sourceUnary, netUnary, basisUnary, _completionUnary, _extensionUnary,
    _transportUnary, sourceNetRefinement, _refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, _localNamePkgFromCarrier⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed netUnary refinementUnary netRefinementRead
  have embeddingReadUnary : UnaryHistory embeddingRead :=
    unary_cont_closed refinementUnary basisUnary refinementBasisRead
  exact
    ⟨netUnary, refinementUnary, refinementReadUnary, embeddingReadUnary,
      sourceNetRefinement, netRefinementRead, refinementBasisRead, localNamePkg⟩

theorem TotallyBoundedCompletionCarrier_route_coverage [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net refinement ∧ Cont refinement basis embedding ∧
        Cont embedding completion separated ∧ Cont separated extension provenance ∧
          Cont transport provenance localName ∧ UnaryHistory refinement ∧
            UnaryHistory embedding ∧ UnaryHistory separated ∧ UnaryHistory provenance ∧
              UnaryHistory localName ∧ PkgSig bundle localName pkg := by
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
    ⟨sourceNetRefinement, refinementBasisEmbedding, embeddingCompletionSeparated,
      separatedExtensionProvenance, transportProvenanceLocalName, refinementUnary, embeddingUnary,
      separatedUnary, provenanceUnary, localNameUnary, localNamePkg⟩

theorem TotallyBoundedCompletionCarrier_root_net_ledger_certificate [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName netRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg ->
      Cont source net netRead ->
        PkgSig bundle netRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row netRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row netRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont source net refinement ∧ Cont source net netRead ∧
                  PkgSig bundle netRead pkg)
              hsame ∧
            UnaryHistory netRead ∧ Cont source net refinement ∧ Cont source net netRead ∧
              PkgSig bundle netRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert UnaryHistory
  intro carrier sourceNetRead netReadPkg
  obtain ⟨sourceUnary, netUnary, _basisUnary, _completionUnary, _extensionUnary,
    _transportUnary, sourceNetRefinement, _refinementBasisEmbedding,
    _embeddingCompletionSeparated, _separatedExtensionProvenance,
    _transportProvenanceLocalName, _provenancePkg, _localNamePkg⟩ := carrier
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed sourceUnary netUnary sourceNetRefinement
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  have sourceAtNetRead : hsame netRead netRead ∧ UnaryHistory netRead :=
    ⟨hsame_refl netRead, netReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row netRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row netRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source net refinement ∧ Cont source net netRead ∧
              PkgSig bundle netRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro netRead sourceAtNetRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceNetRefinement, sourceNetRead, netReadPkg⟩
  }
  exact ⟨cert, netReadUnary, sourceNetRefinement, sourceNetRead, netReadPkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
