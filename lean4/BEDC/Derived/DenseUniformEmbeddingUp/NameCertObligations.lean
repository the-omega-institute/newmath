import BEDC.Derived.DenseUniformEmbeddingUp.LedgerNonescape

namespace BEDC.Derived.DenseUniformEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DenseUniformEmbeddingNameCertObligations [AskSetup] [PackageSetup]
    {source target image modulus embedding extension compatibility transport replay provenance nameRow
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DenseUniformEmbeddingCarrier source target image modulus embedding extension compatibility
        transport replay provenance nameRow bundle pkg ->
      Cont target image routeRead ->
        PkgSig bundle routeRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row target ∨ hsame row image ∨
                  hsame row modulus ∨ hsame row embedding ∨ hsame row extension ∨
                    hsame row routeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont source image modulus ∧
                  Cont modulus embedding extension ∧ Cont target image routeRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory image ∧
              UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: DenseUniformEmbeddingCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier targetImage routePkg
  obtain ⟨sourceUnary, targetUnary, imageUnary, _modulusUnary, _embeddingUnary,
    _extensionUnary, _compatibilityUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameRowUnary, sourceImageModulus, modulusEmbeddingExtension, _compatibilityReplay,
    provenancePkg, _namePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed targetUnary imageUnary targetImage
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row image ∨
              hsame row modulus ∨ hsame row embedding ∨ hsame row extension ∨
                hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source image modulus ∧
              Cont modulus embedding extension ∧ Cont target image routeRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead
        ⟨hsame_refl routeRead, routeReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceImageModulus, modulusEmbeddingExtension, targetImage,
          provenancePkg, routePkg⟩
  }
  exact ⟨cert, sourceUnary, targetUnary, imageUnary, routeReadUnary⟩

end BEDC.Derived.DenseUniformEmbeddingUp
