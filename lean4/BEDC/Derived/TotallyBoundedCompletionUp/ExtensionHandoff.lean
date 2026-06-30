import BEDC.Derived.TotallyBoundedCompletionUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionExtensionHandoff [AskSetup] [PackageSetup]
    {source net refinement basis embedding completion separated extension transport provenance
      localName extensionRead exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier source net refinement basis embedding completion separated
        extension transport provenance localName bundle pkg →
      Cont separated extension extensionRead →
        Cont transport provenance exportedRead →
          PkgSig bundle extensionRead pkg →
            PkgSig bundle exportedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row net ∨ hsame row refinement ∨
                      hsame row basis ∨ hsame row embedding ∨ hsame row completion ∨
                        hsame row separated ∨ hsame row extension ∨
                          hsame row extensionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle extensionRead pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory extensionRead ∧ UnaryHistory exportedRead ∧
                  PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier separatedExtensionRead transportProvenanceExported extensionReadPkg
    _exportedReadPkg
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
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed separatedUnary extensionUnary separatedExtensionRead
  have exportedReadUnary : UnaryHistory exportedRead :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceExported
  have sourceAtExtensionRead : hsame extensionRead extensionRead ∧ UnaryHistory extensionRead :=
    ⟨hsame_refl extensionRead, extensionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row net ∨ hsame row refinement ∨ hsame row basis ∨
              hsame row embedding ∨ hsame row completion ∨ hsame row separated ∨
                hsame row extension ∨ hsame row extensionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle extensionRead pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro extensionRead sourceAtExtensionRead
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, extensionReadPkg, localNamePkg⟩
  }
  exact ⟨cert, extensionReadUnary, exportedReadUnary, localNamePkg⟩

end BEDC.Derived.TotallyBoundedCompletionUp
